import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
namespace ArticuloA.Entropia
open scoped BigOperators

/-- The support and the bad set can depend on n. This estimate transfers the
mean only after the event estimate and an absolute bound on the observable. -/
theorem media_acotada {ι : Type*} (s : Finset ι) (p X : ι → ℝ)
    (a M ε : ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (one : ∑ i ∈ s, p i = 1)
    (cap : ∀ i ∈ s, |X i-a| ≤ M) (ep : 0 ≤ ε) :
    |(∑ i ∈ s, p i * X i)-a| ≤ ε + M*(∑ i ∈ s, if ε < |X i-a| then p i else 0) := by
  classical
  have eq : (∑ i ∈ s, p i*(X i-a)) = (∑ i ∈ s, p i*X i)-a := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,one,one_mul]
  rw [← eq]
  calc _ ≤ ∑ i ∈ s, |p i*(X i-a)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ i ∈ s, (p i * ε + M*(if ε < |X i-a| then p i else 0)) := by
         apply Finset.sum_le_sum
         intro i hi
         rw [abs_mul,abs_of_nonneg (hp i hi)]
         split
         · exact (mul_le_mul_of_nonneg_left (cap i hi) (hp i hi)).trans
             (by rw [mul_comm M]; exact le_add_of_nonneg_left (mul_nonneg (hp i hi) ep))
         · rename_i h
           simpa using mul_le_mul_of_nonneg_left (le_of_not_gt h) (hp i hi)
       _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul,one,one_mul,←Finset.mul_sum]
end ArticuloA.Entropia
#print axioms ArticuloA.Entropia.media_acotada
