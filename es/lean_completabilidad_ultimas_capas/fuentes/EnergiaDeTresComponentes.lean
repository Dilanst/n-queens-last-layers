import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
open MeasureTheory Set
open scoped ENNReal
namespace ArticuloA.Perfil
noncomputable section
def energia {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X→ℝ) :=
  ∫⁻ z, ENNReal.ofReal ((f z)^2) ∂μ
def e2 (x : ℝ) := ENNReal.ofReal (x^2)
theorem e2_med : Measurable e2 :=
  ENNReal.continuous_ofReal.measurable.comp (measurable_id.pow_const 2)
private theorem estimacion_escalar (r d a : ℝ) :
    e2 r≤2*e2 (r+d+a)+4*(e2 d+e2 a) := by
  have sq : r^2≤2*(r+d+a)^2+4*(d^2+a^2) := by
    nlinarith [sq_nonneg (r+2*(d+a)),sq_nonneg (d-a)]
  have h := ENNReal.ofReal_le_ofReal sq
  rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] at h
  simpa [e2] using h

theorem integral_tres {X : Type*} [MeasurableSpace X] (μ : Measure X) (r d a : X→ℝ)
    (hr : Measurable r) (hd : Measurable d) (ha : Measurable a) :
    energia μ r≤2*energia μ (fun z => r z+d z+a z)+4*(energia μ d+energia μ a) := by
  have s := e2_med.comp ((hr.add hd).add ha)
  have sm : Measurable (fun z : X => (2:ℝ≥0∞)*e2 (r z+d z+a z)) := measurable_const.mul s
  have ds : Measurable (fun z : X => e2 (d z)) := e2_med.comp hd
  change (∫⁻ z,e2 (r z) ∂μ)≤_
  calc
    _ ≤ ∫⁻ z,2*e2 (r z+d z+a z)+4*(e2 (d z)+e2 (a z)) ∂μ :=
      lintegral_mono (fun z => estimacion_escalar _ _ _)
    _ = _ := by
      rw [lintegral_add_left sm,lintegral_const_mul' 2 _ (by norm_num),
        lintegral_const_mul' 4 _ (by norm_num),lintegral_add_left ds]
      rfl

end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.integral_tres
