import FibrasDeRegularidad
namespace ArticuloA.Trayectoria.E2
open ArticuloA Regular

def familyPairs : List (Fin 4 × Fin 4) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def shares (a g : Edge) (i : Fin 4) := hitsVertex a (i,g i)
def two (a g : Edge) := familyPairs.any (fun ij => shares a g ij.1 && shares a g ij.2)
def exceptional (L : List Edge) (p a : Edge) :=
  (List.finRange 4).any (shares a p) || L.any (two a)

theorem two_iff (a g : Edge) : two a g ↔ ∃ i j : Fin 4, i < j ∧ a i = g i ∧ a j = g j := by
  constructor
  · intro h
    obtain ⟨⟨i,j⟩,mem,yes⟩ := List.any_eq_true.mp h
    have lt : i<j := by
      simp only [familyPairs,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with eq|eq|eq|eq|eq|eq <;> cases eq <;> decide
    exact ⟨i,j,lt,beq_iff_eq.mp (Bool.and_eq_true_iff.mp yes).1,beq_iff_eq.mp (Bool.and_eq_true_iff.mp yes).2⟩
  · rintro ⟨i,j,lt,hi,hj⟩
    have fin (k : Fin 4) : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
    have mem : (i,j) ∈ familyPairs := by
      rcases fin i with rfl|rfl|rfl|rfl <;> rcases fin j with rfl|rfl|rfl|rfl <;>
        first | decide | exact (False.elim (by omega))
    exact List.any_eq_true.mpr ⟨(i,j),mem,Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr hi,beq_iff_eq.mpr hj⟩⟩

private theorem union2 {X} (L : List X) (P Q : X → Bool) :
    L.countP (fun x => P x || Q x) ≤ L.countP P + L.countP Q := by
  induction L with
  | nil => simp
  | cons x xs ih => simp only [List.countP_cons]; cases P x <;> cases Q x <;> simp_all <;> omega

private theorem many {X Y} (L : List X) (keys : List Y) (test : X → Y → Bool) (b : Nat)
    (each : ∀ j ∈ keys, L.countP (fun x => test x j) ≤ b) :
    L.countP (fun x => keys.any (test x)) ≤ keys.length*b := by
  induction keys with
  | nil => simp
  | cons j js ih =>
    simp only [List.any_cons,List.length_cons,Nat.succ_mul]
    have old := ih (fun i hi => each i (by simp [hi]))
    have h := union2 L (fun x => test x j) (fun x => js.any (test x))
    have k := each j (by simp)
    omega

theorem collisions {X} (L : List X) (edge : X → Edge) (other : List Edge) (p : Edge) (a b : Nat)
    (singleHit : ∀ i, L.countP (fun x => shares (edge x) p i) ≤ a)
    (doubleHit : ∀ g ∈ other, ∀ ij ∈ familyPairs,
      L.countP (fun x => shares (edge x) g ij.1 && shares (edge x) g ij.2) ≤ b) :
    L.countP (fun x => exceptional other p (edge x)) ≤ 4*a + other.length*(6*b) := by
  have s := many L (List.finRange 4) (fun x => shares (edge x) p) a (fun i _ => singleHit i)
  simp only [List.length_finRange] at s
  have d := many L other (fun x => two (edge x)) (6*b) (by
    intro g hg; exact many L familyPairs _ b (doubleHit g hg))
  exact Nat.le_trans (union2 L _ _) (Nat.add_le_add s d)

private theorem distinct_vertices (g : Edge) {ij : Fin 4 × Fin 4} (mem : ij ∈ familyPairs) :
    (ij.1,g ij.1) ≠ (ij.2,g ij.2) := by
  simp only [familyPairs,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl <;> intro eq <;>
    have h := congrArg Prod.fst eq <;> dsimp only at h <;> exact (by decide : ¬ _) h

theorem excepciones_reales (n : Nat) (other : List Edge) (p : Edge) :
    (board n).countP (fun e => exceptional other p (lines e)) ≤ 4*n + other.length*6 := by
  simpa using collisions (board n) lines other p n 1 (fun i => fiber_cap i _)
    (fun g _ ij mem => real_pair_count _ _ (distinct_vertices g mem))

private theorem one_index (N j : Nat) : (List.range N).countP (fun a => a == j) ≤ 1 := by
  have aux (L : List Nat) (nd : L.Nodup) : L.countP (fun a => a == j) ≤ 1 := by
    induction L with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨no,d⟩ := List.nodup_cons.mp nd
      rw [List.countP_cons]
      by_cases h : x=j
      · subst x; have z : xs.countP (fun a => a == j) = 0 :=
          List.countP_eq_zero.mpr (fun a ha eq => no ((beq_iff_eq.mp eq) ▸ ha))
        simp [z]
      · simpa [h] using ih d
  exact aux _ List.nodup_range

theorem virtual_single (N : Nat) (p : Edge) (i : Fin 4) :
    (virtualEdges N).countP (fun x => shares x p i) ≤ N*(N*N) := by
  let f := fun (j : Fin 4) (v : Nat) => if j=i then v == p i else true
  have cases4 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  have rep (x : Edge) : shares x p i = at4 f x := by
    rcases cases4 with rfl|rfl|rfl|rfl <;> simp [shares,hitsVertex,at4,f]
  rw [funext rep,cartesian_count]
  have one := one_index N (p i)
  have h : (List.range N).countP (fun a => a == p i) = 0 ∨
      (List.range N).countP (fun a => a == p i) = 1 := by omega
  rcases cases4 with rfl|rfl|rfl|rfl <;> rcases h with h|h <;> simp [f,h,Nat.mul_assoc]

theorem excepciones_virtuales (N : Nat) (other : List Edge) (p : Edge) :
    (virtualEdges N).countP (exceptional other p) ≤ 4*(N*(N*N)) + other.length*(6*(N*N)) :=
  collisions (virtualEdges N) id other p _ _ (virtual_single N p)
    (fun g _ _ mem => virtual_pair_count _ _ _ (distinct_vertices g mem))

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.two_iff
#print axioms ArticuloA.Trayectoria.E2.excepciones_reales
#print axioms ArticuloA.Trayectoria.E2.excepciones_virtuales
