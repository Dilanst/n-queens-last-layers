import MediasGeometricasDeLosFactores
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

open scoped Topology
def traslacionEnL1 {f : ℝ→ℝ} (hf : Integrable f) (u : ℝ) : Lp ℝ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun t : ℝ=>u+t) (measurePreserving_add_left volume u) (hf.toL1 f)

theorem traslacion_en_L1_continua {f : ℝ→ℝ} (hf : Integrable f) : Continuous (traslacionEnL1 hf) := by
  let g : ℝ → C(ℝ,ℝ) := (ContinuousMap.mk (fun v : ℝ×ℝ=>v.1+v.2) (continuous_fst.add continuous_snd)).curry
  have hp (u : ℝ) : MeasurePreserving (g u) volume volume := measurePreserving_add_left volume u
  exact (show Continuous (fun _ : ℝ=>hf.toL1 f) from continuous_const).compMeasurePreservingLp
    (show Continuous g from ContinuousMap.continuous _) hp (by simp)

theorem distancia_de_los_traslados {f : ℝ→ℝ} (hf : Integrable f) (u v : ℝ) :
    dist (traslacionEnL1 hf u) (traslacionEnL1 hf v)=∫ t : ℝ,|f (t+u)-f (t+v)| := by
  rw [L1.dist_eq_integral_dist]
  have rep (s : ℝ) : (fun t=>(traslacionEnL1 hf s) t)=ᵐ[volume] (fun t=>f (s+t)) := by
    have mp:=measurePreserving_add_left (volume : Measure ℝ) s
    exact (Lp.coeFn_compMeasurePreserving (hf.toL1 f) mp).trans (mp.quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1)
  apply integral_congr_ae
  filter_upwards [rep u,rep v] with t hu hv
  rw [hu,hv,Real.dist_eq,add_comm u t,add_comm v t]

theorem distancia_integral_sobre_rectas {f : ℝ→ℝ} (hf : Integrable f) {a : ℝ} (az : a≠0) (u v l : ℝ) :
    (∫ t in (0:ℝ)..l,|f (a*t+u)-f (a*t+v)|)≤(abs a⁻¹) * dist (traslacionEnL1 hf u) (traslacionEnL1 hf v) := by
  let D t:=|f (t+u)-f (t+v)|
  have it w : Integrable (fun t : ℝ=>f (t+w)) :=
    ((measurePreserving_add_right (volume : Measure ℝ) w).integrable_comp hf.aestronglyMeasurable).mpr hf
  have di : Integrable D := ((it u).sub (it v)).abs
  have dn t : 0≤D t := abs_nonneg _
  rw [distancia_de_los_traslados]
  change (∫ t in (0:ℝ)..l,D (a*t))≤(abs a⁻¹) * ∫ t,D t
  rw [intervalIntegral.integral_comp_mul_left D az,smul_eq_mul]
  apply (le_abs_self _).trans
  rw [abs_mul,intervalIntegral.abs_integral_eq_abs_integral_uIoc,abs_of_nonneg (integral_nonneg dn)]
  exact mul_le_mul_of_nonneg_left (setIntegral_le_integral di (Eventually.of_forall dn)) (abs_nonneg _)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.traslacion_en_L1_continua
#print axioms ArticuloA.Historias.distancia_de_los_traslados
#print axioms ArticuloA.Historias.distancia_integral_sobre_rectas
