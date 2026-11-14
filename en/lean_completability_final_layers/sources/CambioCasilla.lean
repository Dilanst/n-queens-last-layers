import Interpretacion

namespace ArticuloA

/-- Toggle the first occurrence of a square. The board contains each square once. -/
def toggle {n xs} (c : Cell n) (b : @Mask (Cell n) xs) : Mask xs :=
  match b with
  | .empty => .empty
  | .skip (x := x) t => if x = c then .take t else .skip (toggle c t)
  | .take (x := x) t => if x = c then .skip t else .take (toggle c t)

@[simp] theorem toggle_twice {n xs} (c : Cell n) (b : @Mask (Cell n) xs) :
    toggle c (toggle c b) = b := by
  induction b with
  | empty => rfl
  | @skip x _ t ih => by_cases h : x = c <;> simp [toggle, h, ih]
  | @take x _ t ih => by_cases h : x = c <;> simp [toggle, h, ih]

private theorem cells_subset {n xs} (b : @Mask (Cell n) xs) :
    ∀ c ∈ queens b, c ∈ xs := by
  induction b with
  | empty => simp [queens]
  | skip _ ih => intro c hc; exact List.mem_cons_of_mem _ (ih c hc)
  | take _ ih => intro c hc; rcases List.mem_cons.mp hc with e | h
                 · simp [e]
                 · exact List.mem_cons_of_mem _ (ih c h)

private theorem toggle_other {n xs} (c z : Cell n) (b : @Mask (Cell n) xs)
    (hz : z ≠ c) : z ∈ queens (toggle c b) ↔ z ∈ queens b := by
  induction b with
  | empty => rfl
  | @skip x _ t ih => by_cases h : x = c <;> simp [toggle, queens, h, hz, ih]
  | @take x _ t ih => by_cases h : x = c <;> simp [toggle, queens, h, hz, ih]

private theorem toggle_target {n xs} (c : Cell n) (b : @Mask (Cell n) xs)
    (nd : xs.Nodup) (mem : c ∈ xs) :
    (c ∈ queens (toggle c b) ↔ c ∉ queens b) ∧
      (if c ∈ queens b then pieces (toggle c b) + 1 = pieces b
       else pieces (toggle c b) = pieces b + 1) := by
  induction b with
  | empty => simp at mem
  | @skip x xs t ih =>
    obtain ⟨miss, distinct⟩ := List.nodup_cons.mp nd
    by_cases h : x = c
    · subst x
      have absent : c ∉ queens t := fun h => miss (cells_subset t c h)
      simp [toggle, queens, pieces, absent]
    · have H := ih distinct ((List.mem_cons.mp mem).resolve_left (Ne.symm h))
      simpa [toggle, queens, pieces, h, Ne.symm h] using H
  | @take x xs t ih =>
    obtain ⟨miss, distinct⟩ := List.nodup_cons.mp nd
    by_cases h : x = c
    · subst x
      have absent : c ∉ queens t := fun h => miss (cells_subset t c h)
      simp [toggle, queens, pieces, absent]
    · obtain ⟨H, size⟩ := ih distinct ((List.mem_cons.mp mem).resolve_left (Ne.symm h))
      by_cases taken : c ∈ queens t <;>
        simp_all [toggle, queens, pieces, Ne.symm h] <;> omega

abbrev Placement (n : Nat) := Mask (board n)

theorem mem_toggle {n} (c z : Cell n) (b : Placement n) :
    z ∈ queens (toggle c b) ↔ if z = c then z ∉ queens b else z ∈ queens b := by
  by_cases eq : z = c
  · subst z; simpa using (toggle_target c b (board_unique n) (board_complete c)).1
  · simpa [eq] using toggle_other c z b eq

theorem toggle_size {n} (c : Cell n) (b : Placement n) :
    if c ∈ queens b then pieces (toggle c b) + 1 = pieces b
    else pieces (toggle c b) = pieces b + 1 :=
  (toggle_target c b (board_unique n) (board_complete c)).2

/-- In a legal placement any two distinct occupied cells are compatible in either order. -/
theorem legal_pair {n xs} {b : @Mask (Cell n) xs} (h : Legal b) {a c : Cell n}
    (ha : a ∈ queens b) (hc : c ∈ queens b) (ne : a ≠ c) : compatible a c := by
  have sym {x y : Cell n} (p : compatible x y) : compatible y x := by
    obtain ⟨p1,p2,p3,p4⟩ := p
    exact ⟨Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm p4⟩
  have aux (xs : List (Cell n)) (h : xs.Pairwise compatible)
      (ha : a ∈ xs) (hc : c ∈ xs) : compatible a c := by
    induction xs with
    | nil => simp at ha
    | cons x xs ih =>
      obtain ⟨head,tail⟩ := List.pairwise_cons.mp h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact head c ((List.mem_cons.mp hc).resolve_left (Ne.symm ne))
      · rcases List.mem_cons.mp hc with ce | hc
        · subst x
          exact sym (head a ((List.mem_cons.mp ‹a ∈ c :: xs›).resolve_left ne))
        · exact ih tail ha hc
  exact aux _ h ha hc

end ArticuloA
