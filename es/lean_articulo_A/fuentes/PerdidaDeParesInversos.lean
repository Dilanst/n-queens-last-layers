import SoportesPaso
import Diagonales
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

private theorem unicidad {α} (L : List α) (f : α → Bool) (nd : L.Nodup)
    (h : ∀ i ∈ L, ∀ j ∈ L, f i → f j → i=j) : L.countP f ≤ 1 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨no,nd⟩ := List.nodup_cons.mp nd
    rw [List.countP_cons]
    cases fx : f x with
    | false => simpa using ih nd (fun i hi j hj => h i (by simp [hi]) j (by simp [hj]))
    | true =>
      have z : xs.countP f = 0 := List.countP_eq_zero.mpr (by
        intro y hy fy; exact no ((h y (by simp [hy]) x (by simp) fy fx) ▸ hy))
      simp [z]

private theorem dos {α} (L : List α) (f g : α → Bool) :
    L.countP (fun y => f y || g y) ≤ L.countP f + L.countP g := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.countP_cons]; cases f x <;> cases g x <;> simp_all <;> omega

def hitInverse {n} (g e f : Cell n) (plus : Bool) : Bool :=
  if plus then g.1.val+g.2.val == f.1.val+e.2.val
  else g.1.val+e.2.val == f.1.val+g.2.val

theorem two_per_first {n} (p : Placement n) (ok : Legal p) (g e : Cell n) :
    (queens p).countP (fun f => hitInverse g e f true || hitInverse g e f false) ≤ 2 := by
  have nd : (queens p).Nodup := ok.imp (fun h eq => h.1 (congrArg Prod.fst eq))
  have one (b : Bool) : (queens p).countP (fun f => hitInverse g e f b) ≤ 1 := by
    apply unicidad _ _ nd
    intro a ha c hc h₁ h₂
    apply Classical.byContradiction
    intro ne
    have different := (legal_pair ok ha hc ne).1
    apply different; apply Fin.ext
    cases b <;> simp [hitInverse] at h₁ h₂ <;> omega
  exact Nat.le_trans (dos _ _ _) (by have := one true; have := one false; omega)

def hitCount {n} (p : Placement n) (g : Cell n) (es : List (Cell n)) : Nat :=
  (es.map (fun e => (queens p).countP (fun f => hitInverse g e f true || hitInverse g e f false))).sum

theorem hits_old_pairs {n} (p : Placement n) (ok : Legal p) (g : Cell n) :
    hitCount p g (queens p) ≤ 2*n := by
  have bound (L : List (Cell n)) : hitCount p g L ≤ 2*L.length := by
    induction L with
    | nil => simp [hitCount]
    | cons e es ih =>
      change _ + hitCount p g es ≤ _
      have := two_per_first p ok g e
      simp only [List.length_cons]; omega
  have size := distinct_le _ (List.finRange n) (distinctRows ok) (by
    intro j _; simp [List.finRange,List.mem_ofFn])
  simp only [List.length_map,List.length_finRange] at size
  exact Nat.le_trans (bound _) (Nat.mul_le_mul_left _ size)

theorem lost_hits {n} (p : Placement n) (g e f : Cell n) 
    (old : freeDiagonals p (corners (e,f)).2)
    (lost : ¬ freeDiagonals (toggle g p) (corners (e,f)).2) :
    hitInverse g e f true || hitInverse g e f false := by
  classical
  apply Classical.byContradiction
  intro neither
  have ds : diagonalOK g (corners (e,f)).2 := by
    simp [hitInverse] at neither
    exact ⟨neither.2,neither.1⟩
  apply lost
  intro a ha
  by_cases eq : a = g
  · exact eq ▸ ds
  · have was := (mem_toggle g a p).1 ha
    exact old a (by simpa [eq] using was)
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.hits_old_pairs
#print axioms ArticuloA.Trayectoria.E2.lost_hits
