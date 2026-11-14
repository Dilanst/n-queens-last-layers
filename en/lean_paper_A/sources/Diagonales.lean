import Reparaciones

namespace ArticuloA.Repair

def diagonalOK {n} (x y : Cell n) : Prop :=
  x.1.val + y.2.val ≠ y.1.val + x.2.val ∧ x.1.val + x.2.val ≠ y.1.val + y.2.val

def freeDiagonals {n} (u : Placement n) (y : Cell n) : Prop :=
  ∀ x ∈ queens u, diagonalOK x y

private theorem queens_sublist {n xs} (b : @Mask (Cell n) xs) :
    (queens b).Sublist xs := by
  induction b with
  | empty => exact .slnil
  | skip _ ih => exact .cons _ ih
  | take _ ih => exact .cons₂ _ ih

private theorem legal_of_pairs {n} (p : Placement n)
    (hp : ∀ x ∈ queens p, ∀ y ∈ queens p, x ≠ y → compatible x y) : Legal p := by
  have nd := List.Pairwise.sublist (queens_sublist p) (board_unique n)
  exact nd.imp_of_mem (fun hx hy hne => hp _ hx _ hy hne)

private theorem symmetric {n} {x y : Cell n} (c : compatible x y) : compatible y x :=
  ⟨Ne.symm c.1, Ne.symm c.2.1, Ne.symm c.2.2.1, Ne.symm c.2.2.2⟩

private theorem removed_diagonals {n} {a : Mark n} (p : compatible a.1 a.2) :
    diagonalOK a.1 (corners a).2 ∧ diagonalOK a.2 (corners a).2 := by
  have rows : a.1.1.val ≠ a.2.1.val := fun e => p.1 (Fin.ext e)
  have cols : a.1.2.val ≠ a.2.2.val := fun e => p.2.1 (Fin.ext e)
  simp only [diagonalOK, corners]
  omega

private theorem survivors {n} (u : Placement n) (a : Mark n) {x : Cell n}
    (old : x ≠ (corners a).2) (one : x ≠ a.1) (two : x ≠ a.2) :
    x ∈ queens (backward a u) ↔ x ∈ queens u := by
  simp [backward, mem_toggle, old, one, two]

/-- Exact equivalence to the two vacancy indicators appearing in I_w of the paper. -/
theorem inverse_diagonals {n q} (u : Placement n) (a : Mark n)
    (size : pieces u = q+1) (hu : Legal u) (ne : a.1 ≠ a.2)
    (first : a.1 ∈ queens u) (second : a.2 ∈ queens u) :
    Inverse q u a ↔ freeDiagonals u (corners a).2 := by
  let old := (corners a).2
  have comp := legal_pair hu first second ne
  have ao : a.1 ≠ old := fun e => comp.1 (by have eq := congrArg Prod.fst e; exact eq)
  have bo : a.2 ≠ old := fun e => comp.2.1 (by have eq := congrArg Prod.snd e; exact eq.symm)
  have absent : old ∉ queens u := fun h => (legal_pair hu h second (Ne.symm bo)).1 rfl
  have present : old ∈ queens (backward a u) := by
    change old ∈ queens (toggle old (toggle a.1 (toggle a.2 u)))
    simp [mem_toggle, Ne.symm ao, Ne.symm bo, absent]
  have gone1 : a.1 ∉ queens (backward a u) := by
    change a.1 ∉ queens (toggle old (toggle a.1 (toggle a.2 u)))
    simp [mem_toggle, ao, ne, first]
  have gone2 : a.2 ∉ queens (backward a u) := by
    change a.2 ∉ queens (toggle old (toggle a.1 (toggle a.2 u)))
    simp [mem_toggle, bo, Ne.symm ne, second]
  constructor
  · intro inv x hx
    by_cases xa : x = a.1
    · subst x; exact (removed_diagonals comp).1
    by_cases xb : x = a.2
    · subst x; exact (removed_diagonals comp).2
    have xo : x ≠ old := fun eq => absent (eq ▸ hx)
    have inside := (survivors u a xo xa xb).mpr hx
    exact (legal_pair inv.2.2.2.2.2 inside present xo).2.2
  · intro clear
    refine ⟨size, hu, ne, first, second, legal_of_pairs _ ?_⟩
    have stays (x : Cell n) (hx : x ∈ queens (backward a u)) (xo : x ≠ old) :
        x ∈ queens u ∧ compatible x old := by
      have xa : x ≠ a.1 := fun eq => gone1 (eq ▸ hx)
      have xb : x ≠ a.2 := fun eq => gone2 (eq ▸ hx)
      have xu := (survivors u a xo xa xb).mp hx
      exact ⟨xu, (legal_pair hu xu second xb).1, (legal_pair hu xu first xa).2.1, clear x xu⟩
    intro x hx y hy xy
    by_cases xo : x = old
    · subst x; exact symmetric (stays y hy (Ne.symm xy)).2
    by_cases yo : y = old
    · subst y; exact (stays x hx xy).2
    exact legal_pair hu (stays x hx xo).1 (stays y hy yo).1 xy

end ArticuloA.Repair

#print axioms ArticuloA.Repair.inverse_diagonals
