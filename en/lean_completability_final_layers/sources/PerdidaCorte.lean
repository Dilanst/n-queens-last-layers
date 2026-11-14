import PerdidaPaso
import CotaReparaciones

namespace ArticuloA.Repair

/-- Projection of a history to physical placements. A virtual step changes no physical
square. The Nat index counts real insertions only; both ends of a real step are legal. -/
inductive PhysicalTrace {n : Nat} : Placement n → Placement n → Nat → Prop where
  | start (p : Placement n) (legal : Legal p) : PhysicalTrace p p 0
  | virtualStep {p u m} : PhysicalTrace p u m → PhysicalTrace p u m
  | realStep {p u m} (path : PhysicalTrace p u m) (g : Cell n)
      (absent : g ∉ queens u) (legal : Legal (toggle g u)) :
      PhysicalTrace p (toggle g u) (m+1)

theorem PhysicalTrace.final_legal {n} {p u : Placement n} {m}
    (path : PhysicalTrace p u m) : Legal u := by
  induction path with
  | start h => exact h
  | virtualStep _ ih => exact ih
  | realStep _ _ _ h _ => exact h

theorem PhysicalTrace.occupied_persist {n} {p u : Placement n} {m}
    (path : PhysicalTrace p u m) : ∀ e ∈ queens p, e ∈ queens u := by
  induction path with
  | start => exact fun _ h => h
  | virtualStep _ ih => exact ih
  | realStep _ g absent _ ih =>
    intro e h
    exact (inserted _ g absent e).mpr (Or.inr (ih e h))

theorem PhysicalTrace.empty_before {n} {p u : Placement n} {m}
    (path : PhysicalTrace p u m) {z : Cell n} (free : emptyCross u z) : emptyCross p z :=
  fun e he => free e (path.occupied_persist e he)

theorem cut_bounds {n} {p u : Placement n} {m} (path : PhysicalTrace p u m) (z : Cell n) :
    physicalCount p z ≤ physicalCount u z + 4*m ∧
    physicalCount u z ≤ physicalCount p z + m := by
  induction path with
  | start => simp
  | virtualStep _ ih => exact ih
  | realStep prev g absent _ ih =>
    have step := step_counts _ z g prev.final_legal absent
    omega

theorem paper_absolute_change {n} {p u : Placement n} {m} (path : PhysicalTrace p u m)
    (z : Cell n) : ((physicalCount u z : Int) - (physicalCount p z : Int)).natAbs ≤ 5*m := by
  have b := cut_bounds path z
  omega

/-- A surplus of four per remaining real insertion suffices at the cut, simultaneously
for the roots that are empty there. The final root is selected only after the trajectory. -/
theorem threshold_survives {n} {p u : Placement n} {m t} (path : PhysicalTrace p u m)
    (seed : ∀ z, emptyCross p z → t+4*m ≤ physicalCount p z) :
    ∀ z, emptyCross u z → t ≤ crossDegree (pieces u) u z := by
  intro z empty
  have before := seed z (path.empty_before empty)
  have bound := (cut_bounds path z).1
  rw [← physical_eq_crossDegree u z path.final_legal empty]
  omega

/-- Integer cut budget corresponding to the ratio 1/16.
If S is an integer lower bound at the cut, ceil(S/2) survives for S ≥ 20
whenever at most ceil(S/16) real insertions remain. -/
theorem half_seed_survives {n} {p u : Placement n} {m S} (path : PhysicalTrace p u m)
    (large : 20 ≤ S) (budget : m ≤ (S+15)/16)
    (seed : ∀ z, emptyCross p z → S ≤ physicalCount p z) :
    ∀ z, emptyCross u z → (S+1)/2 ≤ crossDegree (pieces u) u z := by
  apply threshold_survives path
  intro z free
  have initial := seed z free
  omega

/-- Any final event whose configurations have such a successful physical history
provides a deterministic lower bound. Its probability is a separate obligation. -/
theorem cut_event_le_fh (n h t : Nat) (hh : 0 < h) (hq : 0 < n-h)
    (pos : 0 < count n (n-h)) (G : Placement n → Prop)
    (witness : ∀ u, Legal u → pieces u = n-h → G u →
      ∃ p m, PhysicalTrace p u m ∧ ∀ z, emptyCross p z → t+4*m ≤ physicalCount p z) :
    Std.Internal.mkRat (Int.ofNat (t * eventCount h G)) (count n (n-h) * (n-h)) ≤ fh n h hh pos := by
  apply event_fraction_le_fh n h t hh hq pos
  intro u legal size good
  obtain ⟨p,m,path,seed⟩ := witness u legal size good
  have every := threshold_survives path seed
  rw [size] at every
  have holes : n-(n-h) = h := by omega
  simpa only [holes] using many_of_each_cross u legal size t every

end ArticuloA.Repair

#print axioms ArticuloA.Repair.cut_bounds
#print axioms ArticuloA.Repair.paper_absolute_change
#print axioms ArticuloA.Repair.threshold_survives
#print axioms ArticuloA.Repair.half_seed_survives
#print axioms ArticuloA.Repair.cut_event_le_fh
