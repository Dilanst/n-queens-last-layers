import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
open scoped BigOperators
namespace ArticuloA.Revelado
noncomputable section
open Classical
variable {ι : Type*} [DecidableEq ι]

/-- Conditional on the clock of the distinguished piece, U consists of the
other pieces, and T is the subset whose independent clocks are later. -/
def masa (U T : Finset ι) (z : ℝ) := z^T.card * (1-z)^(U\T).card

theorem supervivencia (U K : Finset ι) (subset : K ⊆ U) (z : ℝ) :
    ∑ T ∈ U.powerset, (if K ⊆ T then masa U T z else 0) = z^K.card := by
  let g := fun i => if i ∈ K then (0:ℝ) else 1-z
  have term (T : Finset ι) :
      (if K ⊆ T then masa U T z else 0) = (∏ _ ∈ T,z)*(∏ i ∈ U\T,g i) := by
    by_cases h : K ⊆ T
    · rw [if_pos h,masa,Finset.prod_const]
      apply congrArg (fun a => z^T.card*a)
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro i hi
      simp [g,show i ∉ K from fun hk => (Finset.mem_sdiff.mp hi).2 (h hk)]
    · obtain ⟨i,ik,it⟩ := Finset.not_subset.mp h
      have hit : i ∈ U\T := Finset.mem_sdiff.mpr ⟨subset ik,it⟩
      rw [if_neg h,Finset.prod_eq_zero hit (show g i=0 by simp [g,ik]),mul_zero]
  rw [Finset.sum_congr rfl (fun T _ => term T),←Finset.prod_add]
  have one (i : ι) : z+g i = if i ∈ K then z else 1 := by
    by_cases h : i∈K <;> simp [g,h]
  simp_rw [one]
  rw [Finset.prod_ite_mem,Finset.inter_eq_right.mpr subset,Finset.prod_const]

theorem normalizada (U : Finset ι) (z : ℝ) : ∑ T ∈ U.powerset, masa U T z = 1 := by
  simpa using supervivencia U ∅ (Finset.empty_subset _) z

/-- Each candidate can share owners with any other candidate. Only the
indicators that the specified owners survive are used in this expectation. -/
theorem media_normalizador {α : Type*} (U : Finset ι) (A : Finset α)
    (owners : α → Finset ι) (sub : ∀ e ∈ A, owners e ⊆ U) (w : α → ℝ) (z : ℝ) :
    ∑ T ∈ U.powerset, masa U T z * (∑ e ∈ A, if owners e ⊆ T then w e else 0) =
      ∑ e ∈ A, w e * z^(owners e).card := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e he
  rw [←supervivencia U (owners e) (sub e he) z,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro T _
  split_ifs <;> simp [mul_comm]

/-- The three classes have 4, at least 1, and 0 other owners, respectively. -/
theorem cota_tres_clases {α : Type*} (U : Finset ι) (A : Finset α)
    (owners : α → Finset ι) (sub : ∀ e ∈ A, owners e ⊆ U) (w : α → ℝ)
    (nn : ∀ e ∈ A, 0≤w e) (z : ℝ) (h0 : 0≤z) (h1 : z≤1) :
    ∑ T ∈ U.powerset, masa U T z * (∑ e ∈ A, if owners e ⊆ T then w e else 0) ≤
      (∑ e ∈ A,w e)*z^4 + (∑ e ∈ A, if (owners e).card≠4 then w e else 0)*z +
      (∑ e ∈ A, if owners e=∅ then w e else 0) := by
  rw [media_normalizador U A owners sub,Finset.sum_mul,Finset.sum_mul,←Finset.sum_add_distrib,
    ←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  have W := nn e he
  by_cases h : (owners e).card=4
  · have ne : owners e ≠ ∅ := by intro eq; simp [eq] at h
    simp [h,ne]
  · by_cases em : owners e=∅
    · simp [em]; nlinarith [mul_nonneg W (pow_nonneg h0 4),mul_nonneg W h0]
    · have k := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em)
      have p : z^(owners e).card ≤ z := by
        simpa using (pow_le_pow_of_le_one h0 h1 (show 1 ≤ (owners e).card by omega))
      simp only [h,ne_eq,not_false_eq_true,if_true,em,if_false,add_zero]
      linarith [mul_le_mul_of_nonneg_left p W,mul_nonneg W (pow_nonneg h0 4)]
end
end ArticuloA.Revelado
#print axioms ArticuloA.Revelado.supervivencia
#print axioms ArticuloA.Revelado.media_normalizador
#print axioms ArticuloA.Revelado.cota_tres_clases
