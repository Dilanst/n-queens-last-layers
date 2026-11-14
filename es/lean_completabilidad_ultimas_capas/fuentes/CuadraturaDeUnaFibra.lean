import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
open MeasureTheory Set
open scoped BigOperators Interval
namespace ArticuloA.Perfil
noncomputable section

theorem error_en_intervalo (f : ℝ→ℝ) (a b z L : ℝ) (ab : a≤b) (az : a≤z) (zb : z≤b)
    (cont : IntervalIntegrable f volume a b) (lp : 0≤L)
    (oscilacion : ∀ x∈Icc a b, |f x-f z|≤L*|x-z|) :
    |(∫ x in a..b,f x)-(b-a)*f z|≤L*(b-a)^2 := by
  have diff : (∫ x in a..b,f x-f z)=(∫ x in a..b,f x)-(b-a)*f z := by
    rw [intervalIntegral.integral_sub cont intervalIntegrable_const,intervalIntegral.integral_const,smul_eq_mul]
  rw [←diff]
  have geb (x : ℝ) (mem : x∈uIoc a b) : ‖f x-f z‖≤L*(b-a) := by
    rw [uIoc_of_le ab] at mem
    obtain ⟨hx,xb⟩ := mem
    exact (oscilacion x ⟨hx.le,xb⟩).trans (mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith,by linarith⟩) lp)
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const geb
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ab)] at bound
  simpa only [pow_two,mul_assoc] using bound

theorem cuadratura_finita (n : ℕ) (m z : ℕ→ℝ) (f : ℝ→ℝ) (L : ℝ) (lp : 0≤L)
    (mon : ∀ i<n,m i≤m (i+1)) (centro : ∀ i<n,z i∈Icc (m i) (m (i+1)))
    (intg : ∀ i<n,IntervalIntegrable f volume (m i) (m (i+1)))
    (lip : ∀ i<n,∀ x∈Icc (m i) (m (i+1)),|f x-f (z i)|≤L*|x-z i|) :
    |(∫ x in (m 0)..(m n),f x) - ∑ i∈Finset.range n,(m (i+1)-m i)*f (z i)|≤
      L*∑ i∈Finset.range n,(m (i+1)-m i)^2 := by
  rw [←intervalIntegral.sum_integral_adjacent_intervals (a:=m) intg,←Finset.sum_sub_distrib,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi => by
    have h := Finset.mem_range.mp hi
    exact error_en_intervalo f _ _ _ L (mon i h) (centro i h).1 (centro i h).2 (intg i h) lp (lip i h)))
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.cuadratura_finita
