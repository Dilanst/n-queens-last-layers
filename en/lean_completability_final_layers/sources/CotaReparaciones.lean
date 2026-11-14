import Grados
import Fracciones

namespace ArticuloA.Repair

private theorem sum_eq_masks {n} (xs : List (Cell n)) (f : Mask xs → Nat) :
    sumMasks xs f = counting.masks xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change sumMasks xs _ + sumMasks xs _ = counting.masks xs _ + counting.masks xs _
    rw [ih, ih]

theorem sum_mono {α xs} (f g : @Mask α xs → Nat) (bound : ∀ p, f p ≤ g p) :
    sumMasks xs f ≤ sumMasks xs g := by
  induction xs with
  | nil => exact bound .empty
  | cons x xs ih =>
    exact Nat.add_le_add (ih _ _ (fun p => bound (.skip p))) (ih _ _ (fun p => bound (.take p)))

theorem sum_times {α xs} (f : @Mask α xs → Nat) (k : Nat) :
    sumMasks xs (fun p => f p * k) = sumMasks xs f * k := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumMasks, ih, Nat.add_mul]

noncomputable def directTotal (n q : Nat) := sumMasks (board n) (directDegree q)
noncomputable def inverseTotal (n q : Nat) := sumMasks (board n) (inverseDegree q)

theorem totals_equal (n q : Nat) : directTotal n q = inverseTotal n q := by
  unfold directTotal inverseTotal
  rw [sum_eq_masks, sum_eq_masks]
  exact weighted_double_count counting q (fun _ => 1)

theorem total_bound (n q : Nat) : directTotal n q ≤ count n (q+1) * ((q+1)*q) := by
  rw [totals_equal]
  unfold inverseTotal count
  rw [← sum_times]
  exact sum_mono _ _ (fun u => inverseDegree_le u)

theorem no_repairs_on_empty_board (n : Nat) : directTotal n 0 = 0 ∧ inverseTotal n 0 = 0 := by
  have bound := total_bound n 0
  have eq := totals_equal n 0
  simp at bound
  exact ⟨bound, eq ▸ bound⟩

/-- Mean direct degree divided by h²q, represented as the one exact fraction
total degree / (N_h h²q). Invalid configurations contribute zero by Direct. -/
noncomputable def normalizedDirectMean (n h : Nat) (_ : 0 < h) (_ : 0 < n-h)
    (_ : 0 < count n (n-h)) : Std.Internal.Rat :=
  Std.Internal.mkRat (Int.ofNat (directTotal n (n-h))) (h^2 * count n (n-h) * (n-h))

/-- The unit-weight inequality of the double-counting lemma (Section 6), with the same f_h as in (1.1). -/
theorem normalizedDirectMean_le_fh (n h : Nat) (hh : 0 < h) (hq : 0 < n-h)
    (pos : 0 < count n (n-h)) : normalizedDirectMean n h hh hq pos ≤ fh n h hh pos := by
  have upper : n-(h-1) = n-h+1 := by omega
  have den : 0 < h^2 * count n (n-h) := Nat.mul_pos (Nat.pow_pos hh) pos
  apply ratio_le_of_cross (Nat.mul_pos den hq) den
  rw [upper]
  let q := n-h
  let base := h^2 * count n q
  change directTotal n q * base ≤ ((q+1)*count n (q+1)) * (base*q)
  calc
    _ ≤ (count n (q+1) * ((q+1)*q)) * base := Nat.mul_le_mul_right _ (total_bound n q)
    _ = _ := by ac_rfl

open Classical in
noncomputable def eventCount {n} (h : Nat) (G : Placement n → Prop) :=
  sumMasks (board n) (fun p => if G p then layer (n-h) p else 0)

theorem cota_evento_cruda (n h t : Nat) (G : Placement n → Prop)
    (many : ∀ p, Legal p → pieces p = n-h → G p → h^2*t ≤ directDegree (n-h) p) :
    eventCount h G * (h^2*t) ≤ count n (n-h+1) * ((n-h+1)*(n-h)) := by
  classical
  let q := n-h
  have lower : eventCount h G * (h^2*t) ≤ directTotal n q := by
    unfold eventCount directTotal
    rw [← sum_times]
    apply sum_mono
    intro p
    by_cases good : G p
    · by_cases belongs : Legal p ∧ pieces p = n-h
      · simpa [good, layer, belongs, q] using many p belongs.1 belongs.2 good
      · simp [good, layer, belongs]
    · simp [good]
  exact Nat.le_trans lower (total_bound n q)

/-- Finite event bound. t is an integer lower bound on the degree per cross
on average over the h² crosses of each member of G in the lower layer. -/
theorem event_fraction_le_fh (n h t : Nat) (hh : 0 < h) (hq : 0 < n-h)
    (pos : 0 < count n (n-h)) (G : Placement n → Prop)
    (many : ∀ p, Legal p → pieces p = n-h → G p → h^2*t ≤ directDegree (n-h) p) :
    Std.Internal.mkRat (Int.ofNat (t * eventCount h G)) (count n (n-h) * (n-h)) ≤
      fh n h hh pos := by
  classical
  let q := n-h
  have combined := cota_evento_cruda n h t G many
  have upper : n-(h-1) = q+1 := by dsimp [q]; omega
  apply ratio_le_of_cross (Nat.mul_pos pos hq) (Nat.mul_pos (Nat.pow_pos hh) pos)
  rw [upper]
  calc
    _ = (eventCount h G * (h^2*t)) * count n q := by dsimp [q]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right (count n q) combined
    _ = _ := by dsimp [q]; ac_rfl

/-- G is precisely the event that every empty cross has at least t legal repairs. -/
theorem all_crosses_event_bound (n h t : Nat) (hh : 0 < h) (hq : 0 < n-h)
    (pos : 0 < count n (n-h)) :
    Std.Internal.mkRat (Int.ofNat (t * eventCount (n := n) h (fun p =>
      ∀ z, emptyCross p z → t ≤ crossDegree (n-h) p z))) (count n (n-h) * (n-h)) ≤
      fh n h hh pos := by
  apply event_fraction_le_fh n h t hh hq pos
  intro p legal size good
  have holes : n-(n-h) = h := by omega
  simpa only [holes] using many_of_each_cross p legal size t good

end ArticuloA.Repair

#print axioms ArticuloA.Repair.total_bound
#print axioms ArticuloA.Repair.no_repairs_on_empty_board
#print axioms ArticuloA.Repair.normalizedDirectMean_le_fh
#print axioms ArticuloA.Repair.event_fraction_le_fh
#print axioms ArticuloA.Repair.all_crosses_event_bound
