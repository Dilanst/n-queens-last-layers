import AdjuncionDeEulerBajoContinuidad
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Interval
-- Argumento local de unicidad.
private theorem unicidad_por_pruebas_continuas (i : Fin 4) {f g : ℝ→ℝ}
    (fc : ContinuousOn f (rangoF i)) (gc : ContinuousOn g (rangoF i))
    (eq : ∀ v : ℝ→ℝ,Continuous v →
      (∫ t,f t*v t ∂marginalRef i)=∫ t,g t*v t ∂marginalRef i) : f=ᵐ[marginalRef i] g := by
  let v:=fun t => (f-g) (recorte i t)
  have vc : Continuous v := (fc.sub gc).comp_continuous
    (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)
  have ref : marginalRef i=volume.restrict (rangoF i) := by
    have oc : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [oc]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have fi : Integrable (fun t => f t*v t) (marginalRef i) := by rw [ref]; exact (fc.mul vc.continuousOn).integrableOn_Icc
  have gi : Integrable (fun t => g t*v t) (marginalRef i) := by rw [ref]; exact (gc.mul vc.continuousOn).integrableOn_Icc
  have support : ∀ᵐ t ∂marginalRef i,t∈rangoF i := by rw [ref]; exact ae_restrict_mem measurableSet_Icc
  have nn : 0≤ᵐ[marginalRef i] (fun t => f t*v t-g t*v t) := by
    filter_upwards [support] with t ht
    change (0:ℝ)≤f t*v t-g t*v t
    dsimp only [v,Pi.sub_apply]; rw [recorte_fijo i ht]; nlinarith [sq_nonneg (f t-g t)]
  have iz : (∫ t,f t*v t-g t*v t ∂marginalRef i)=0 := by rw [integral_sub fi gi,eq v vc,sub_self]
  have ae:=(integral_eq_zero_iff_of_nonneg_ae nn (fi.sub gi)).mp iz
  filter_upwards [ae,support] with t hz ht
  change f t*((f-g) (recorte i t))-g t*((f-g) (recorte i t))=0 at hz
  rw [recorte_fijo i ht,Pi.sub_apply] at hz
  have sq : (f t-g t)^2=0 := by nlinarith only [hz]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp sq)

theorem ecuaciones_de_fibra_desde_euler_medida {P p x b} (e : EulerFisica P p x b)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (i : Fin 4) :
    ∀ᵐ s ∂marginalRef i,b*integralFisica p i s=1-holguraLinea p x i s := by
  have fc : ContinuousOn (fun s=>b*integralFisica p i s) (rangoF i) := by
    apply ((continuousOn_const (c:=b)).mul ((cp i).mul (cavidad_continua_con_factores_continuos cp i))).congr
    intro s _; exact congrArg (b*·) (factor_de_la_familia_por_su_cavidad p i s)
  have gc : ContinuousOn (fun s=>1-holguraLinea p x i s) (rangoF i) := continuousOn_const.sub (continuousOn_const.mul (cp i))
  apply unicidad_por_pruebas_continuas i fc gc
  intro w wc
  rw [←probar_integrales_fisicas_continuas b cp i w wc]
  calc
    _ = (∫ z,(P.ν z:ℝ)*w (coord i z) ∂cuadrado) := by
      apply integral_congr_ae; filter_upwards [e.real] with z hz; rw [hz]
    _ = ∫ s,(P.m i s:ℝ)*w s ∂marginalRef i := adjuncion P.ley i w wc.measurable
    _ = _ := by
      apply integral_congr_ae; filter_upwards [e.linea i] with s hs
      apply congrArg (·*w s)
      unfold TableroMedido.u at hs; linarith only [hs]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ecuaciones_de_fibra_desde_euler_medida
