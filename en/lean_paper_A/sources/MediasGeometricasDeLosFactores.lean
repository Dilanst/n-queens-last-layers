import JensenEnLasMedidasFisicas
import LaCotaR7SobreUnaFibraTransversal
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
noncomputable local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩

def mediaGeometrica (r : ℝ→ℝ) := exp (∫ t,log (r t) ∂unidad)
def costoTotalR7 (p : FactoresContinuos) (x : ℝ≥0) := masaLogOblicua p x 2+masaLogOblicua p x 3
def nucleoEnUnaTransversal (p : FactoresContinuos) (x : ℝ≥0) (col : Bool) (s t : ℝ) :=
  holguraInteriorR5 p x 2 (if col then t-s else s-t)*holguraInteriorR5 p x 3 (s+t)

theorem integral_en_el_intervalo_unitario (f : ℝ→ℝ) :
    (∫ t,f t ∂unidad)=∫ t in (0:ℝ)..1,f t := by
  rw [unidad,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]

theorem promedio_ponderado_de_la_fibra {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (col : Bool) {r : ℝ→ℝ} (rc : Continuous r) (rp : ∀ t,0<r t) :
    mediaGeometrica r*exp (-costoTotalR7 p x) ≤ ∫ t,r t*nucleoEnUnaTransversal p x col s t ∂unidad := by
  let D (t : ℝ):=holguraInteriorR5 p x 2 (if col then t-s else s-t)
  let A (t : ℝ):=holguraInteriorR5 p x 3 (s+t)
  have info:=vacancia_fisica_y_logaritmo e xp cp pos
  have dc : Continuous D := by
    cases col
    · exact (info 2).1.comp (continuous_const.sub continuous_id)
    · exact (info 2).1.comp (continuous_id.sub continuous_const)
  have ac : Continuous A := (info 3).1.comp (continuous_const.add continuous_id)
  have dp t : 0<D t := (info 2).2.1 _
  have ap t : 0<A t := (info 3).2.1 _
  let f (t : ℝ):=r t*(D t*A t)
  have fc : Continuous f := rc.mul (dc.mul ac)
  have fp t : 0<f t := mul_pos (rp t) (mul_pos (dp t) (ap t))
  have it {g : ℝ→ℝ} (cg : Continuous g) : Integrable g unidad := cg.continuousOn.integrableOn_Icc
  have posInt : 0<∫ t,f t ∂unidad := by
    apply lt_of_le_of_ne (integral_nonneg (fun t=>(fp t).le))
    intro hz
    have ae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun t=>(fp t).le)) (it fc)).mp hz.symm
    obtain ⟨t,ht⟩:=ae.exists
    exact (fp t).ne' ht
  have base:=jensen_log_en_una_probabilidad (Eventually.of_forall fp) (it fc) (it (fc.log (fun t=>(fp t).ne'))) posInt
  have dl:=it (dc.log (fun t=>(dp t).ne'))
  have al:=it (ac.log (fun t=>(ap t).ne'))
  have rl:=it (rc.log (fun t=>(rp t).ne'))
  have cell t : log (f t)=log (r t)+(log (D t)+log (A t)) := by
    unfold f; rw [log_mul (rp t).ne' (mul_pos (dp t) (ap t)).ne',log_mul (dp t).ne' (ap t).ne']
  have bound := costo_fisico_de_las_diagonales e xp cp pos s hs col
  change (∫ t in (0:ℝ)..1,-log (D t)+ -log (A t)) ≤ costoTotalR7 p x at bound
  have nd : Integrable (fun t=> -log (D t)) unidad := dl.neg
  have na : Integrable (fun t=> -log (A t)) unidad := al.neg
  rw [←integral_en_el_intervalo_unitario,integral_add nd na,integral_neg,integral_neg] at bound
  have addint : Integrable (fun t=>log (D t)+log (A t)) unidad := dl.add al
  simp_rw [cell] at base
  rw [integral_add rl addint,integral_add dl al] at base
  unfold mediaGeometrica
  rw [←exp_add]
  exact (exp_le_exp.mpr (by linarith only [bound])).trans base
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_en_el_intervalo_unitario
#print axioms ArticuloA.Historias.promedio_ponderado_de_la_fibra
