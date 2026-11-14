import PruebasContinuasParaLasOblicuas
import LasDosMarginalesRectasDeEuler
import DirectaDelArticuloConElPesoContinuo
open Set Filter MeasureTheory
open scoped Interval NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

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

theorem euler_oblicua_puntual {P p x b κ M L} (e : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (lp : 0≤L) (anti : Bool) :
    let i:=indiceDeLaSeccion anti
    ∀ t∈rangoF i,b*integralFisica p i t=1-holguraLinea p x i t := by
  intro i
  have fc:=continuousOn_const (c:=b) |>.mul (integral_fisica_continua sp lp i)
  have gc : ContinuousOn (fun t => 1-holguraLinea p x i t) (rangoF i) :=
    continuousOn_const.sub (continuousOn_const.mul (continua_de_cota lp (regular_familia sp i).oscilacion))
  apply euler_puntual_de_fibras_ae sp lp x i
  apply unicidad_por_pruebas_continuas i fc gc
  intro v vc
  rw [←prueba_de_la_marginal_oblicua e sp lp anti vc]
  apply integral_congr_ae
  filter_upwards [e.linea i] with t h
  have eq : (P.m i t:ℝ)=1-holguraLinea p x i t := by unfold TableroMedido.u at h; linarith
  rw [eq]

/-- All four physical fibers, including both ends of the oblique supports. -/
theorem euler_puntual_de_la_rama {P p b κ M L B} (rama : RamaDensa P p b κ M L B) :
    EulerPuntualDeRama p b := by
  intro x hx i
  have e:=rama.euler x hx
  have sp:=rama.espacio x hx
  fin_cases i
  · exact integral_euler_en_rectas e sp rama.lp 0 (by decide)
  · exact integral_euler_en_rectas e sp rama.lp 1 (by decide)
  · exact euler_oblicua_puntual e sp rama.lp false
  · exact euler_oblicua_puntual e sp rama.lp true

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_puntual_de_la_rama
