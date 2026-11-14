import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory
open scoped Interval
theorem integra_tres_errores {d K : ℝ} (hd : 0≤d) {F H : ℝ→ℝ} {e : Fin 3→ℝ→ℝ}
    (cf : ContinuousOn F (Icc 0 d)) (ch : ContinuousOn H (Icc 0 d))
    (ce : ∀ j,ContinuousOn (e j) (Icc 0 d))
    (h : ∀ t∈Icc 0 d,|F t-H t|≤K*(e 0 t+e 1 t+e 2 t)) :
    |(∫ t in (0:ℝ)..d,F t)-(∫ t in (0:ℝ)..d,H t)| ≤
      K*((∫ t in (0:ℝ)..d,e 0 t)+(∫ t in (0:ℝ)..d,e 1 t)+(∫ t in (0:ℝ)..d,e 2 t)) := by
  have intg {f : ℝ→ℝ} (hf : ContinuousOn f (Icc 0 d)) : IntervalIntegrable f volume 0 d :=
    (by simpa [uIcc_of_le hd] using hf : ContinuousOn f (uIcc 0 d)).intervalIntegrable
  rw [←intervalIntegral.integral_sub (intg cf) (intg ch)]
  apply (intervalIntegral.abs_integral_le_integral_abs hd).trans
  have mono:=intervalIntegral.integral_mono_on hd (intg (cf.sub ch).abs)
    (intg (continuousOn_const.mul (((ce 0).add (ce 1)).add (ce 2)))) h
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (intg ((ce 0).add (ce 1))) (intg (ce 2)),
    intervalIntegral.integral_add (intg (ce 0)) (intg (ce 1))] at mono
  exact mono

theorem suma_de_tres_raices {a b c : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    Real.sqrt a+Real.sqrt b+Real.sqrt c≤Real.sqrt 3*Real.sqrt (a+b+c) := by
  have root:=Real.sq_sqrt (add_nonneg (add_nonneg ha hb) hc)
  have r3:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have right : 0≤Real.sqrt 3*Real.sqrt (a+b+c) := by positivity
  apply le_of_sq_le_sq _ right
  rw [mul_pow,r3,root]
  nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb,Real.sq_sqrt hc,
    sq_nonneg (Real.sqrt a-Real.sqrt b),sq_nonneg (Real.sqrt b-Real.sqrt c),
    sq_nonneg (Real.sqrt a-Real.sqrt c)]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integra_tres_errores
#print axioms ArticuloA.Historias.suma_de_tres_raices
