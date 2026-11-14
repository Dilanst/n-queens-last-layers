import RepresentanteFisicoDeLosCuatroLimites
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Real

/-- The reference measure on a row-label or column-label interval has mass one. -/
theorem covarianza_de_una_holgura_y_su_log {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {x : ℝ} (xp : 0<x) {u : α→ℝ} (pos : ∀ᵐ s ∂μ,0<u s)
    (ui : Integrable u μ) (masa : ∫ s,u s ∂μ=x)
    (wi : Integrable (fun s=>(u s-x)*log (u s)) μ) : 0≤∫ s,(u s-x)*log (u s) ∂μ := by
  have a : ∀ᵐ s ∂μ, (u s-x)*log x ≤ (u s-x)*log (u s) := by
    filter_upwards [pos] with s ps
    by_cases h : x≤u s
    · exact mul_le_mul_of_nonneg_left (log_le_log xp h) (sub_nonneg.mpr h)
    · exact mul_le_mul_of_nonpos_left (log_le_log ps (le_of_not_ge h)) (sub_nonpos.mpr (le_of_not_ge h))
  have hi : Integrable (fun s=>(u s-x)*log x) μ := (ui.sub (integrable_const x)).mul_const _
  have z : (∫ s,(u s-x)*log x ∂μ)=0 := by
    rw [integral_mul_const,integral_sub ui (integrable_const x),masa]; simp
  exact z ▸ integral_mono_ae hi wi a

theorem absorcion_puntual_del_logaritmo {κ δ u m₀ : ℝ} (kp : 0<κ) (k1 : κ≤1)
    (dr : δ≤1) (up : 0<u) (u1 : u≤1) (mp : 0≤m₀) (ms : m₀≤1-κ) :
    (κ/2)*(-log u) ≤ (1-u-δ*m₀)*(-log u)+(1+κ/2)*log (2/κ) := by
  have lnon : 0≤ -log u := neg_nonneg.mpr (log_nonpos up.le u1)
  have z : 0≤log (2/κ) := log_nonneg ((le_div_iff₀ kp).mpr (by linarith))
  have pro : δ*m₀≤m₀ := by nlinarith [mul_nonneg (sub_nonneg.mpr dr) mp]
  by_cases h : u≤κ/2
  · have coef : κ/2≤1-u-δ*m₀ := by linarith
    linarith only [mul_le_mul_of_nonneg_right coef lnon,mul_nonneg (by linarith only [kp] : 0≤1+κ/2) z]
  · have logle : -log u≤log (2/κ) := by
      rw [←Real.log_inv]
      exact log_le_log (inv_pos.mpr up) ((inv_le_comm₀ up (div_pos (by norm_num) kp)).mpr (by
        rw [inv_div]; linarith only [le_of_not_ge h]))
    have coef : 0≤1+(1-u-δ*m₀) := by linarith
    nlinarith only [mul_nonneg coef lnon,mul_le_mul_of_nonneg_left logle (by linarith only [kp] : 0≤1+κ/2)]

theorem integral_oblicua_desde_la_comparacion {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {κ δ : ℝ} {u m₀ : α→ℝ} (kp : 0<κ) (k1 : κ≤1)
    (dr : δ≤1) (bounds : ∀ᵐ s ∂μ,0<u s ∧ u s≤1 ∧ 0≤m₀ s ∧ m₀ s≤1-κ)
    (li : Integrable (fun s=> -log (u s)) μ)
    (ri : Integrable (fun s=>(1-u s-δ*m₀ s)*(-log (u s))) μ) :
    (κ/2)*(∫ s,-log (u s) ∂μ) ≤ (∫ s,(1-u s-δ*m₀ s)*(-log (u s)) ∂μ)+
      μ.real univ*((1+κ/2)*log (2/κ)) := by
  have h:=integral_mono_ae (li.const_mul (κ/2)) (ri.add (integrable_const ((1+κ/2)*log (2/κ))))
    (bounds.mono (fun s hs=>absorcion_puntual_del_logaritmo kp k1 dr hs.1 hs.2.1 hs.2.2.1 hs.2.2.2))
  simp only [Pi.add_apply,integral_const_mul,integral_add ri (integrable_const _),integral_const,smul_eq_mul] at h
  linarith only [h]

theorem constante_R7_para_las_dos_oblicuas {κ M E H_R H_C D A L_D L_A : ℝ} (kp : 0<κ)
    (balance : E+H_R+H_C+D+A=0) (entropy : -M-1/exp 1≤E) (row : 0≤H_R) (col : 0≤H_C)
    (diag : κ/2*L_D≤D+2*((1+κ/2)*log (2/κ))) (anti : κ/2*L_A≤A+2*((1+κ/2)*log (2/κ))) :
    L_D+L_A≤(2/κ)*(M+1/exp 1+4*log (2/κ))+4*log (2/κ) := by
  apply (le_of_mul_le_mul_left ?_ kp)
  rw [mul_add,mul_add,←mul_assoc,show κ*(2/κ)=2 by field_simp]
  linarith only [balance,entropy,row,col,diag,anti]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.covarianza_de_una_holgura_y_su_log
#print axioms ArticuloA.Historias.absorcion_puntual_del_logaritmo
#print axioms ArticuloA.Historias.integral_oblicua_desde_la_comparacion
#print axioms ArticuloA.Historias.constante_R7_para_las_dos_oblicuas
