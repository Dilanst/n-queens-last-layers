import Diagonales

namespace ArticuloA.Repair

/-- Only the additive laws are required; weights need not be nonnegative. -/
structure SumLaw (α : Type) where
  zero : α
  plus : α → α → α
  zero_add : ∀ a, plus zero a = a
  comm : ∀ a b, plus a b = plus b a
  assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)

namespace SumLaw
variable {α : Type} (s : SumLaw α)

def over {β} (xs : List β) (f : β → α) : α :=
  xs.foldr (fun x acc => s.plus (f x) acc) s.zero

def masks {n} : (xs : List (Cell n)) → (Mask xs → α) → α
  | [], f => f .empty
  | _::xs, f => s.plus (masks xs (fun p => f (.skip p)))
                         (masks xs (fun p => f (.take p)))

private theorem exchange (a b c d : α) :
    s.plus (s.plus a b) (s.plus c d) = s.plus (s.plus a c) (s.plus b d) := by
  rw [s.assoc, ← s.assoc b c d, s.comm b c, s.assoc c b d, ← s.assoc]

private theorem over_plus {β} (xs : List β) (f g : β → α) :
    s.over xs (fun x => s.plus (f x) (g x)) = s.plus (s.over xs f) (s.over xs g) := by
  induction xs with
  | nil => exact (s.zero_add _).symm
  | cons x xs ih =>
    change s.plus _ (s.over xs _) = s.plus (s.plus _ _) (s.plus _ _)
    rw [ih]; apply s.exchange

private theorem over_zero {β} (xs : List β) : s.over xs (fun _ => s.zero) = s.zero := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => change s.plus s.zero _ = _; rw [s.zero_add]; exact ih

private theorem interchange {β γ} (xs : List β) (ys : List γ) (f : β → γ → α) :
    s.over xs (fun x => s.over ys (fun y => f x y)) =
    s.over ys (fun y => s.over xs (fun x => f x y)) := by
  induction xs with
  | nil => exact (s.over_zero ys).symm
  | cons x xs ih =>
    change s.plus (s.over ys _) (s.over xs _) =
      s.over ys (fun y => s.plus (f x y) (s.over xs (fun z => f z y)))
    rw [s.over_plus, ih]

private theorem masks_over {n β} (xs : List (Cell n)) (ys : List β) (f : Mask xs → β → α) :
    s.masks xs (fun p => s.over ys (f p)) = s.over ys (fun y => s.masks xs (fun p => f p y)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change s.plus (s.masks xs _) (s.masks xs _) = s.over ys (fun y =>
      s.plus (s.masks xs (fun p => f (.skip p) y)) (s.masks xs (fun p => f (.take p) y)))
    rw [s.over_plus, ih (fun p y => f (.skip p) y), ih (fun p y => f (.take p) y)]

def marks {n} (f : Mark n → α) : α :=
  let idx := List.finRange n
  s.over idx (fun r => s.over idx (fun c => s.over idx (fun i => s.over idx (fun j =>
    f ((r,c),(i,j))))))

private theorem masks_marks {n} (f : Placement n → Mark n → α) :
    s.masks (board n) (fun p => s.marks (f p)) =
    s.marks (fun m => s.masks (board n) (fun p => f p m)) := by
  simp only [marks, masks_over]

private theorem reverse_indices {β} (xs : List β) (f : β → β → β → α) :
    s.over xs (fun a => s.over xs (fun b => s.over xs (fun c => f a b c))) =
    s.over xs (fun c => s.over xs (fun b => s.over xs (fun a => f a b c))) := by
  calc
    _ = s.over xs (fun b => s.over xs (fun a => s.over xs (fun c => f a b c))) := s.interchange _ _ _
    _ = s.over xs (fun b => s.over xs (fun c => s.over xs (fun a => f a b c))) := by
      apply congrArg (s.over xs); funext b; apply s.interchange
    _ = _ := s.interchange _ _ _

private theorem marks_corners {n} (f : Mark n → α) :
    s.marks f = s.marks (fun m => f (corners m)) := by
  unfold marks
  apply congrArg (s.over _)
  funext r
  exact s.reverse_indices _ (fun c i j => f ((r,c),(i,j)))

private theorem masks_toggle {n} (xs : List (Cell n)) (c : Cell n) (f : Mask xs → α) :
    s.masks xs (fun p => f (toggle c p)) = s.masks xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases eq : x = c
    · simp only [masks, toggle, if_pos eq]; apply s.comm
    · simp only [masks, toggle, if_neg eq]
      rw [ih (fun t => f (.skip t)), ih (fun t => f (.take t))]

private theorem masks_forward {n} (m : Mark n) (f : Placement n → α) :
    s.masks (board n) (fun p => f (forward m p)) = s.masks (board n) f := by
  unfold forward
  rw [s.masks_toggle _ m.2 (fun p => f (toggle (corners m).2 (toggle (corners m).1 p))),
      s.masks_toggle _ (corners m).1 (fun p => f (toggle (corners m).2 p)), s.masks_toggle]

end SumLaw

open Classical in
noncomputable def directWeight {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α)
    (p : Placement n) (m : Mark n) : α := if Direct q p m then w m.1 else s.zero

open Classical in
noncomputable def inverseWeight {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α)
    (u : Placement n) (a : Mark n) : α := if Inverse q u a then w (corners a).1 else s.zero

private theorem transported {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α)
    (p : Placement n) (m : Mark n) :
    directWeight s q w p m = inverseWeight s q w (forward m p) (corners m) := by
  have iff : Direct q p m ↔ Inverse q (forward m p) (corners m) :=
    ⟨forward_valid, fun h => by simpa using backward_valid h⟩
  by_cases h : Direct q p m
  · simp [directWeight, inverseWeight, h, iff.mp h]
  · have h' : ¬ Inverse q (forward m p) (corners m) := fun v => h (iff.mpr v)
    simp only [directWeight, inverseWeight, if_neg h, if_neg h']

/-- Integer-count (unnormalized) form of the double-counting identity (Section 6), valid also for signed weights. -/
theorem weighted_double_count {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α) :
    s.masks (board n) (fun p => s.marks (directWeight s q w p)) =
    s.masks (board n) (fun u => s.marks (inverseWeight s q w u)) := by
  rw [s.masks_marks, s.masks_marks]
  calc
    _ = s.marks (fun m => s.masks (board n) (fun u => inverseWeight s q w u (corners m))) := by
      apply congrArg s.marks
      funext m
      simp only [transported s q w]
      exact s.masks_forward m (fun u => inverseWeight s q w u (corners m))
    _ = _ := (s.marks_corners (fun m : Mark n => s.masks (board n)
      (fun u => inverseWeight s q w u m))).symm

open Classical in
/-- Inverse summand as printed in the manuscript, using both diagonals in the upper board. -/
noncomputable def diagonalWeight {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α)
    (u : Placement n) (a : Mark n) : α :=
  if pieces u = q+1 ∧ Legal u ∧ a.1 ≠ a.2 ∧ a.1 ∈ queens u ∧ a.2 ∈ queens u ∧
     freeDiagonals u (corners a).2 then w (corners a).1 else s.zero

private theorem inverseWeight_diagonal {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α)
    (u : Placement n) (a : Mark n) : inverseWeight s q w u a = diagonalWeight s q w u a := by
  classical
  let allowed := pieces u = q+1 ∧ Legal u ∧ a.1 ≠ a.2 ∧ a.1 ∈ queens u ∧ a.2 ∈ queens u ∧
                 freeDiagonals u (corners a).2
  have same : Inverse q u a ↔ allowed := by
    constructor
    · intro h
      obtain ⟨sz, hu, ne, p1, p2, _⟩ := (show Inverse q u a from h)
      exact ⟨sz, hu, ne, p1, p2, (inverse_diagonals u a sz hu ne p1 p2).mp h⟩
    · rintro ⟨sz, hu, ne, p1, p2, free⟩
      exact (inverse_diagonals u a sz hu ne p1 p2).mpr free
  change (if Inverse q u a then _ else _) = (if allowed then _ else _)
  by_cases h : Inverse q u a
  · simp only [if_pos h, if_pos (same.mp h)]
  · have no : ¬ allowed := fun yes => h (same.mpr yes)
    simp only [if_neg h, if_neg no]

theorem paper_double_count {n α} (s : SumLaw α) (q : Nat) (w : Cell n → α) :
    s.masks (board n) (fun p => s.marks (directWeight s q w p)) =
    s.masks (board n) (fun u => s.marks (diagonalWeight s q w u)) := by
  rw [weighted_double_count]
  have same (u : Placement n) : inverseWeight s q w u = diagonalWeight s q w u :=
    funext (inverseWeight_diagonal s q w u)
  simp only [same]

end ArticuloA.Repair

#print axioms ArticuloA.Repair.direct_roundtrip
#print axioms ArticuloA.Repair.inverse_roundtrip
#print axioms ArticuloA.Repair.weighted_double_count
#print axioms ArticuloA.Repair.paper_double_count
