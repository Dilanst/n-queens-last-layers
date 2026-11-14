import CandidatoFisico

namespace ArticuloA.Repair

noncomputable def tally {α : Type} (xs : List α) (P : α → Prop) : Nat :=
  counting.over xs (fun e => indicator (P e))

private theorem tally_zero {α : Type} (xs : List α) (P : α → Prop) (no : ∀ x ∈ xs, ¬P x) :
    tally xs P = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change indicator (P x) + tally xs P = 0
    rw [ih (fun y hy => no y (by simp [hy]))]
    simp [indicator,no x (by simp)]

private theorem tally_one {α : Type} (xs : List α) (P : α → Prop) (nd : xs.Nodup)
    (unique : ∀ x y, P x → P y → x = y) : tally xs P ≤ 1 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nd
    change indicator (P x) + tally xs P ≤ 1
    by_cases h : P x
    · rw [tally_zero xs P (by intro y hy py; exact absent ((unique y x py h) ▸ hy))]
      simp [indicator,h]
    · simpa [indicator,h] using ih tail

private theorem tally_union4 {α : Type} (xs : List α) (P A B C D : α → Prop)
    (cover : ∀ x, P x → A x ∨ B x ∨ C x ∨ D x) :
    tally xs P ≤ tally xs A + tally xs B + tally xs C + tally xs D := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have one : indicator (P x) ≤ indicator (A x) + indicator (B x) +
        indicator (C x) + indicator (D x) := by
      by_cases h : P x
      · rcases cover x h with a|b|c|d <;> simp_all [indicator] <;> omega
      · simp [indicator,h]
    change indicator (P x) + tally xs P ≤ (indicator (A x) + tally xs A) +
      (indicator (B x) + tally xs B) + (indicator (C x) + tally xs C) +
      (indicator (D x) + tally xs D)
    omega

private theorem balance {α : Type} (xs : List α) (P Q : α → Prop) :
    tally xs P + tally xs (fun x => Q x ∧ ¬P x) =
      tally xs Q + tally xs (fun x => P x ∧ ¬Q x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (indicator (P x) + tally xs P) + (indicator _ + tally xs _) =
      (indicator (Q x) + tally xs Q) + (indicator _ + tally xs _)
    by_cases p : P x <;> by_cases q : Q x <;> simp [indicator,p,q] <;> omega

/-- The four ways that g can block a destination, first along the row and then along the column. -/
def hit {n} (z g e : Cell n) : Fin 4 → Prop
  | 0 => g.1.val + e.2.val = z.1.val + g.2.val
  | 1 => g.1.val + g.2.val = z.1.val + e.2.val
  | 2 => g.1.val + z.2.val = e.1.val + g.2.val
  | 3 => g.1.val + g.2.val = e.1.val + z.2.val

private theorem hit_unique {n} {p : Placement n} (hp : Legal p) (z g : Cell n) (s : Fin 4)
    (x y : Cell n) (hx : x ∈ queens p ∧ hit z g x s) (hy : y ∈ queens p ∧ hit z g y s) :
    x = y := by
  by_cases eq : x = y
  · exact eq
  have comp := legal_pair hp hx.1 hy.1 eq
  have cols : x.2.val ≠ y.2.val := fun v => comp.2.1 (Fin.ext v)
  have rows : x.1.val ≠ y.1.val := fun v => comp.1 (Fin.ext v)
  have a := hx.2
  have b := hy.2
  have cases4 : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases cases4 with rfl | rfl | rfl | rfl <;> simp only [hit] at a b <;> omega

/-- Physical occupancy after inserting one previously absent queen. -/
theorem inserted {n} (p : Placement n) (g : Cell n) (empty : g ∉ queens p) (x : Cell n) :
    x ∈ queens (toggle g p) ↔ x = g ∨ x ∈ queens p := by
  by_cases eq : x = g <;> simp [mem_toggle,eq,empty]

private theorem new_only {n} (p : Placement n) (z g e : Cell n) (empty : g ∉ queens p)
    (now : Candidate (toggle g p) z e) (before : ¬Candidate p z e) : e = g := by
  obtain ⟨occ, geom, a, b⟩ := now
  rcases (inserted p g empty e).mp occ with eq | old
  · exact eq
  · exact (before ⟨old,geom, fun x hx => a x ((inserted p g empty x).mpr (.inr hx)),
                    fun x hx => b x ((inserted p g empty x).mpr (.inr hx))⟩).elim

private theorem loss_hits {n} (p : Placement n) (z g e : Cell n) (empty : g ∉ queens p)
    (old : Candidate p z e) (lost : ¬Candidate (toggle g p) z e) :
    hit z g e 0 ∨ hit z g e 1 ∨ hit z g e 2 ∨ hit z g e 3 := by
  apply Classical.byContradiction
  intro no
  obtain ⟨occ,geom,clearA,clearB⟩ := old
  apply lost
  refine ⟨(inserted p g empty e).mpr (.inr occ),geom,?_,?_⟩
  · intro x hx
    rcases (inserted p g empty x).mp hx with rfl | hx
    · exact ⟨fun v => no (.inl v), fun v => no (.inr (.inl v))⟩
    · exact clearA x hx
  · intro x hx
    rcases (inserted p g empty x).mp hx with rfl | hx
    · exact ⟨fun v => no (.inr (.inr (.inl v))), fun v => no (.inr (.inr (.inr v)))⟩
    · exact clearB x hx

noncomputable def deaths {n} (p u : Placement n) (z : Cell n) :=
  tally (board n) (fun e => Candidate p z e ∧ ¬Candidate u z e)
noncomputable def births {n} (p u : Placement n) (z : Cell n) :=
  tally (board n) (fun e => Candidate u z e ∧ ¬Candidate p z e)

theorem real_step {n} (p : Placement n) (z g : Cell n) (hp : Legal p) (empty : g ∉ queens p) :
    deaths p (toggle g p) z ≤ 4 ∧ births p (toggle g p) z ≤ 1 := by
  let killed (s : Fin 4) (e : Cell n) := e ∈ queens p ∧ hit z g e s
  have single (s : Fin 4) : tally (board n) (killed s) ≤ 1 :=
    tally_one _ _ (board_unique n) (hit_unique hp z g s)
  constructor
  · have total := tally_union4 (board n) _ (killed 0) (killed 1) (killed 2) (killed 3) (by
      intro e (h : Candidate p z e ∧ ¬Candidate (toggle g p) z e)
      rcases loss_hits p z g e empty h.1 h.2 with a|b|c|d
      · exact .inl ⟨h.1.1,a⟩
      · exact .inr (.inl ⟨h.1.1,b⟩)
      · exact .inr (.inr (.inl ⟨h.1.1,c⟩))
      · exact .inr (.inr (.inr ⟨h.1.1,d⟩)))
    have a := single 0; have b := single 1; have c := single 2; have d := single 3
    unfold deaths
    omega
  · apply tally_one _ _ (board_unique n)
    intro x y hx hy
    exact (new_only p z g x empty hx.1 hx.2).trans (new_only p z g y empty hy.1 hy.2).symm

theorem step_counts {n} (p : Placement n) (z g : Cell n) (hp : Legal p) (empty : g ∉ queens p) :
    physicalCount p z ≤ physicalCount (toggle g p) z + 4 ∧
    physicalCount (toggle g p) z ≤ physicalCount p z + 1 := by
  obtain ⟨loss,gain⟩ := real_step p z g hp empty
  have eq := balance (board n) (Candidate p z) (Candidate (toggle g p) z)
  change physicalCount p z + births p (toggle g p) z =
    physicalCount (toggle g p) z + deaths p (toggle g p) z at eq
  omega

end ArticuloA.Repair
#print axioms ArticuloA.Repair.real_step
