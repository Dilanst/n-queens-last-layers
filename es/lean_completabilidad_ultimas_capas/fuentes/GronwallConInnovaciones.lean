import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open scoped BigOperators
namespace ArticuloA.Seguimiento

/-- A stopped path. Up to and including the exit transition, its discrepancy is
a cumulative innovation plus the predictable errors of its coordinates. -/
theorem cota_de_trayectoria {ι : Type*} (E : ℕ → ℝ) (D M : ι → ℕ → ℝ)
    (T : ℕ) (g L : ℝ) (hL : 0 ≤ L)
    (drift : ∀ i t, t < T → |D i t| ≤ L*(E t + 1))
    (ruido : ∀ i t, t ≤ T → |M i t| ≤ g)
    (coord : ∀ t ≤ T, ∃ i, E t ≤ |M i t + ∑ j ∈ Finset.range t, D i j|) :
    ∀ t ≤ T, E t + 1 ≤ (g+1)*(1+L)^t := by
  have prev (t) (ht : t ≤ T) : E t+1 ≤ g+1 + ∑ j ∈ Finset.range t, L*(E j + 1) := by
    obtain ⟨i,hi⟩ := coord t ht
    have A := abs_add_le (M i t) (∑ j ∈ Finset.range t, D i j)
    have B := Finset.abs_sum_le_sum_abs (D i) (Finset.range t)
    have C := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range t) =>
      drift i j (lt_of_lt_of_le (Finset.mem_range.mp hj) ht))
    linarith [ruido i t ht]
  have envelope (t : ℕ) : g+1 + ∑ j ∈ Finset.range t, L*((g+1)*(1+L)^j) = (g+1)*(1+L)^t := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, ←add_assoc, ih, pow_succ]; ring
  intro t ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
    rw [←envelope]
    apply (prev t ht).trans
    apply add_le_add_left
    apply Finset.sum_le_sum
    intro j hj
    have before := Finset.mem_range.mp hj
    exact mul_le_mul_of_nonneg_left (ih j before (le_trans before.le ht)) hL

end ArticuloA.Seguimiento
#print axioms ArticuloA.Seguimiento.cota_de_trayectoria
