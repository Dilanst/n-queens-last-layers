import TangenteSinSupuestoDePositividadDelRival
open MeasureTheory Filter Set
namespace ArticuloA.Historias
open Perfil
noncomputable section
theorem jensen_log_en_una_probabilidad {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {t : α→ℝ} (tp : ∀ᵐ y ∂μ,0<t y) (ti : Integrable t μ)
    (li : Integrable (fun y=>Real.log (t y)) μ) (mp : 0<∫ y,t y ∂μ) :
    Real.exp (∫ y,Real.log (t y) ∂μ) ≤ ∫ y,t y ∂μ := by
  let m:=∫ y,t y ∂μ
  have c (y : α) (yp : 0<t y) : m*Real.log (t y) ≤ t y-m+m*Real.log m := by
    have h:=xlogx_tangente (x:=t y) (y:=m) yp mp.le
    unfold xlogx at h; linarith only [h]
  have hi:=integral_mono_ae (li.const_mul m) ((ti.sub (integrable_const m)).add (integrable_const (m*Real.log m)))
    (tp.mono c)
  change (∫ y,m*Real.log (t y) ∂μ)≤∫ y,(t y-m)+m*Real.log m ∂μ at hi
  have hc : Integrable (fun y=>t y-m) μ := ti.sub (integrable_const m)
  rw [integral_const_mul,integral_add hc (integrable_const (m*Real.log m)),
    integral_sub ti (integrable_const m)] at hi
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hi
  have z : (∫ y,t y ∂μ)-m=0 := sub_self m
  rw [z,zero_add] at hi
  calc
    Real.exp (∫ y,Real.log (t y) ∂μ) ≤ Real.exp (Real.log m) := Real.exp_le_exp.mpr (le_of_mul_le_mul_left hi mp)
    _ = m := Real.exp_log mp

theorem jensen_entropia_de_una_densidad {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {t : α→ℝ} (tp : ∀ᵐ y ∂μ,0≤t y) (ti : Integrable t μ)
    (xi : Integrable (fun y=>xlogx (t y)) μ) (mp : 0<∫ y,t y ∂μ) :
    xlogx (∫ y,t y ∂μ)≤∫ y,xlogx (t y) ∂μ := by
  let m:=∫ y,t y ∂μ
  have h:=integral_mono_ae ((ti.add (ti.mul_const (Real.log m))).sub (integrable_const m)) xi
    (tp.mono (fun y hy=>xlogx_tangente mp hy))
  change (∫ y,(t y+t y*Real.log m)-m ∂μ)≤_ at h
  have ai : Integrable (fun y=>t y+t y*Real.log m) μ := ti.add (ti.mul_const _)
  rw [integral_sub ai (integrable_const m),integral_add ti (ti.mul_const (Real.log m)),integral_mul_const] at h
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at h
  change m+m*Real.log m-m≤_ at h
  simpa only [add_sub_cancel_left,xlogx] using h
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.jensen_log_en_una_probabilidad
#print axioms ArticuloA.Historias.jensen_entropia_de_una_densidad
