import SeccionesFisicasDelTestigoDeDEF
import CamposNormalizadosParaLaTraslacion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Real
open scoped Topology Interval
theorem continua_la_proyeccion_del_testigo (a : Bool) : Continuous (proyeccionDelTestigo a) := by
  let F (s t : ℝ):=testigoDEF34 (t+max s 0) (if a then 1-(t+max (-s) 0) else t+max (-s) 0)
  let xy (v : ℝ×ℝ) : ℝ×ℝ := (v.2+max v.1 0,if a then 1-(v.2+max (-v.1) 0) else v.2+max (-v.1) 0)
  have xc : Continuous xy := by cases a <;> dsimp [xy] <;> fun_prop
  have comp : Continuous (Function.uncurry F) := by
    change Continuous (densidadTestigo ∘ xy)
    exact Continuous.comp (g:=densidadTestigo) (f:=xy) densidad_testigo_continua xc
  change Continuous (fun s=>∫ t in (0:ℝ)..(1-|s|),F s t)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume)
    (a₀:=(0:ℝ)) (s:=fun s : ℝ=>1-|s|) comp (continuous_const.sub continuous_id.abs)

theorem continua_la_marginal_del_testigo (i : Fin 4) : Continuous (marginalDelTestigo i) := by
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact continua_la_proyeccion_del_testigo false
  · exact (continua_la_proyeccion_del_testigo true).comp (continuous_id.sub continuous_const)

theorem integral_cuadrada_de_una_continua {f : ℝ×ℝ→ℝ} (fc : Continuous f) : Integrable f cuadrado := by
  rw [cuadrado,unidad,Measure.prod_restrict]
  exact fc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem integral_de_etiqueta_de_una_continua (i : Fin 4) {f : ℝ→ℝ} (fc : Continuous f) :
    Integrable f (marginalRef i) := by
  have h : marginalRef i=volume.restrict (rangoF i) := by
    have a : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [a]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [h]; exact fc.continuousOn.integrableOn_Icc

theorem masa_unitaria_del_testigo : ∫ z,densidadTestigo z ∂cuadrado=1 := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  have h:=pruebas_continuas_con_el_testigo 0 (fun _=>(1:ℝ)) continuous_const
  have ref : marginalRef 0=unidad := Measure.restrict_congr_set Ioc_ae_eq_Icc
  simpa [ref,marginalDelTestigo] using h

/-- Qualitative, pointwise positivity on the compact label ranges suffices here. -/
theorem log_de_euler_en_un_parametro_interior {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i))
    (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    (∀ i,Continuous (campoPerfil p x i)) ∧
    ∀ᵐ z ∂cuadrado,log (P.ν z)=log (b/(x:ℝ)^2)+∑ i : Fin 4,campoPerfil p x i (coord i z) := by
  have pz i s : 0<campoR15 p i s := pos i _ (recorte_dentro i s)
  refine ⟨fun i=>continuous_const.add ((campo_continuo_por_recorte cp i).log (fun s=>(pz i s).ne')),?_⟩
  filter_upwards [densidad_en_factores_recortados e] with z eq
  have logeq:=log_del_producto (y:=fun i=>campoR15 p i (coord i z)) e.coef (fun i=>pz i _) eq
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have total : (∑ i : Fin 4,correccionRC x i)=2*log (x:ℝ) := by
    rw [Fin.sum_univ_four]; norm_num [correccionRC,show ¬(3:Fin 4).val<2 by decide]; ring
  have split (i : Fin 4) : campoPerfil p x i (coord i z)=correccionRC x i+log (campoR15 p i (coord i z)) := rfl
  rw [logeq,log_div e.coef.ne' (pow_ne_zero 2 xr.ne'),log_pow]
  simp_rw [split,Finset.sum_add_distrib,total]
  ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.continua_la_proyeccion_del_testigo
#print axioms ArticuloA.Historias.continua_la_marginal_del_testigo
#print axioms ArticuloA.Historias.integral_cuadrada_de_una_continua
#print axioms ArticuloA.Historias.integral_de_etiqueta_de_una_continua
#print axioms ArticuloA.Historias.masa_unitaria_del_testigo
#print axioms ArticuloA.Historias.log_de_euler_en_un_parametro_interior
