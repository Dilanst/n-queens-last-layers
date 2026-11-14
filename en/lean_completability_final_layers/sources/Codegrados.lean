import MediaEntera
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

private theorem productCount {α β} (xs : List α) (rows : α → List β) (p : β → Bool)
    (q : α → Bool) (m : Nat) (each : ∀ a, (rows a).countP p = if q a then m else 0) :
    (xs.flatMap rows).countP p = xs.countP q*m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons,List.countP_append,each,ih,List.countP_cons]
    cases h : q a <;> simp [h,Nat.add_mul,Nat.add_comm]

def at4 (f : Fin 4 → Nat → Bool) (v : Edge) :=
  f 0 (v 0) && f 1 (v 1) && f 2 (v 2) && f 3 (v 3)

theorem cartesian_count (N : Nat) (f : Fin 4 → Nat → Bool) :
    (virtualEdges N).countP (at4 f) = (List.range N).countP (f 0) *
      ((List.range N).countP (f 1) * ((List.range N).countP (f 2) * (List.range N).countP (f 3))) := by
  let r := List.range N
  unfold virtualEdges
  apply productCount r; intro i
  cases h0 : f 0 i with
  | false =>
    simp [List.countP_eq_zero,List.mem_flatMap,List.mem_map,at4,h0]
    rintro _ _ _ _ _ _ _ rfl; simp [h0]
  | true =>
    simp only [if_true]
    apply productCount r; intro j
    cases h1 : f 1 j with
    | false =>
      simp [List.countP_eq_zero,List.mem_flatMap,List.mem_map,at4,h1]
      rintro _ _ _ _ _ rfl; simp [h1]
    | true =>
      simp only [if_true]; apply productCount r; intro d
      simp only [List.countP_map]; cases h2 : f 2 d <;> simp [Function.comp_def,at4,h0,h1,h2]

private theorem single {N v : Nat} : (List.range N).countP (fun i => i == v) ≤ 1 := by
  have aux (L : List Nat) (nd : L.Nodup) : L.countP (fun i => i == v) ≤ 1 := by
    induction L with
    | nil => simp
    | cons i L ih =>
      obtain ⟨absent,h⟩ := List.nodup_cons.mp nd
      rw [List.countP_cons]; by_cases eq : i=v
      · subst i; have no : L.countP (fun j => j==v) = 0 := List.countP_eq_zero.mpr (by
          intro j hj yes; exact absent ((beq_iff_eq.mp yes) ▸ hj))
        simp [no]
      · simpa [eq] using ih h
  exact aux _ List.nodup_range

def hitsVertex (g : Edge) (v : Vertex) := g v.1 == v.2
theorem virtual_pair_count (N : Nat) (v w : Vertex) (ne : v ≠ w) :
    (virtualEdges N).countP (fun g => hitsVertex g v && hitsVertex g w) ≤ N*N := by
  obtain ⟨i,a⟩ := v; obtain ⟨j,b⟩ := w
  by_cases eq : i=j
  · subst j; have ab : a ≠ b := fun h => ne (h ▸ rfl)
    have h (g : Edge) : (hitsVertex g (i,a) && hitsVertex g (i,b)) = false := by
      simp [hitsVertex]; intro x; exact fun y => ab (x.symm.trans y)
    simp [h]
  · let f := fun (l : Fin 4) u => if l=i then u==a else if l=j then u==b else true
    have cf (k : Fin 4) : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    have rep (g : Edge) : (hitsVertex g (i,a) && hitsVertex g (j,b)) = at4 f g := by
      rcases cf i with rfl|rfl|rfl|rfl <;> rcases cf j with rfl|rfl|rfl|rfl <;>
        first | exact (eq rfl).elim | simp [hitsVertex,at4,f,Bool.and_comm]
    rw [funext rep,cartesian_count]
    have small (u : Nat) := @single N u
    have split (u : Nat) : (List.range N).countP (fun i => i==u) = 0 ∨
        (List.range N).countP (fun i => i==u) = 1 := by have := small u; omega
    rcases cf i with rfl|rfl|rfl|rfl <;> rcases cf j with rfl|rfl|rfl|rfl <;>
      first | exact (eq rfl).elim | (rcases split a with ha|ha <;> rcases split b with hb|hb <;> simp [f,ha,hb])

theorem real_pair_count {n} (v w : Vertex) (ne : v ≠ w) :
    (board n).countP (fun c => hitsVertex (lines c) v && hitsVertex (lines c) w) ≤ 1 := by
  let p := fun (c : Cell n) => hitsVertex (lines c) v && hitsVertex (lines c) w
  have uniq {c e : Cell n} (hc : p c) (he : p e) : c=e := by
    simp [p,hitsVertex] at hc he
    by_cases eq : v.1 = w.1
    · have bad : v.2=w.2 := by rw [← hc.1,eq,hc.2]
      exact (ne (Prod.ext eq bad)).elim
    · exact real_codegree c e _ _ eq (hc.1.trans he.1.symm) (hc.2.trans he.2.symm)
  let xs := (board n).filter p
  have nd : xs.Nodup := (board_unique n).filter _
  rw [List.countP_eq_length_filter]
  change xs.length ≤ 1
  cases hx : xs with
  | nil => simp
  | cons a tl =>
    cases ht : tl with
    | nil => simp
    | cons b rest =>
      rw [ht] at hx
      have ha : a ∈ xs := by simp [hx]
      have hb : b ∈ xs := by simp [hx]
      have eq := uniq (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2
      rw [hx] at nd; exact ((List.nodup_cons.mp nd).1 (by simp [eq])).elim

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.virtual_pair_count
#print axioms ArticuloA.Trayectoria.E2.real_pair_count
