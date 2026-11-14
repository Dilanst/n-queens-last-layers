import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
open Filter
open scoped Topology
open scoped BigOperators
namespace ArticuloA.Entropia

/-- On the support of the first law only; the second law can have extra atoms.
U is a tilt whose total mass under the second law is at most 2. -/
theorem inclinacion {ι : Type*} (S : Finset ι) (p q U : ι → ℝ)
    (hp : ∀ i ∈ S, 0 < p i) (hq : ∀ i ∈ S, 0 < q i) (hu : ∀ i ∈ S, 0 < U i)
    (one : ∑ i ∈ S, p i = 1) (two : ∑ i ∈ S, q i * U i ≤ 2) :
    ∑ i ∈ S, p i * Real.log (U i) ≤
      (∑ i ∈ S, p i * Real.log (p i/q i)) + Real.log 2 := by
  have pt (i) (hi : i ∈ S) :
      p i * Real.log (U i) - p i * Real.log (p i/q i) - p i * Real.log 2
        ≤ q i * U i / 2 - p i := by
    have P := hp i hi
    have Q := hq i hi
    have V := hu i hi
    have H := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (show 0 < q i * U i / (2 * p i) by positivity)) P.le
    rw [Real.log_div (mul_pos Q V).ne' (by positivity),
      Real.log_mul Q.ne' V.ne', Real.log_mul (by norm_num) P.ne'] at H
    rw [Real.log_div P.ne' Q.ne']
    have eq : p i * (q i * U i / (2*p i) - 1) = q i*U i/2-p i := by
      field_simp [P.ne']; ring
    rw [eq] at H
    linarith
  have H := Finset.sum_le_sum pt
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, one, one_mul] at H
  linarith

/-- The count of bad leaves is tested with the same terminal weight as the KL.
The good part can have total q mass strictly less than one. -/
theorem coste_binario {ι : Type*} (S : Finset ι) (p q : ι → ℝ) (bad : ι → Bool) (t : ℝ)
    (hp : ∀ i ∈ S, 0 < p i) (hq : ∀ i ∈ S, 0 < q i) (one : ∑ i ∈ S, p i = 1)
    (prob : ∑ i ∈ S, q i ≤ 1)
    (raro : (∑ i ∈ S, if bad i then q i else 0) * Real.exp t ≤ 1) :
    (∑ i ∈ S, if bad i then p i else 0) * t ≤
      (∑ i ∈ S, p i * Real.log (p i/q i)) + Real.log 2 := by
  let U i := if bad i then Real.exp t else 1
  have pt (i) (hi : i ∈ S) : q i * U i ≤ q i + (if bad i then q i else 0)*Real.exp t := by
    cases v : bad i <;> simp [U,v,(hq i hi).le]
  have H := Finset.sum_le_sum pt
  rw [Finset.sum_add_distrib, ←Finset.sum_mul] at H
  have app := inclinacion S p q U hp hq (fun i _ => by cases v : bad i <;> simp [U,v,Real.exp_pos]) one (by linarith)
  rw [Finset.sum_mul]
  convert app using 1
  apply Finset.sum_congr rfl; intro i _
  cases v : bad i <;> simp [U,v]

end ArticuloA.Entropia
#print axioms ArticuloA.Entropia.coste_binario
