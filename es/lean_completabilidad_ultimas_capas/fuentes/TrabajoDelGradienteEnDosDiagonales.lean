import AdjuncionDeLaDensidadTrasladada
import IntegrabilidadDeLasCargasDeFranja
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
private theorem areaIntegrable {f : ℝ×ℝ→ℝ} (cf : Continuous f) : Integrable f cuadrado := by
  rw [cuadrado,unidad,Measure.prod_restrict]
  exact cf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem trabajo_por_las_tres_proyecciones {U : ℝ×ℝ→ℝ} {r d a : ℝ→ℝ}
    (cu : Continuous U) (cr : Continuous r) (cd : Continuous d) (ca : Continuous a) :
    (∫ z,U z*sumaLevantada false r d a z ∂cuadrado)=
      (∫ s,(∫ t in (0:ℝ)..1,U (s,t))*r s ∂unidad)+
      (∫ s,cargaDeFranja U 1 s*d s ∂diag)+(∫ s,cargaDeFranja U 2 s*a s ∂anti) := by
  let fr:=fun z : ℝ×ℝ=>U z*r z.1
  let fd:=fun z : ℝ×ℝ=>U z*d (z.1-z.2)
  let fa:=fun z : ℝ×ℝ=>U z*a (z.1+z.2)
  have ir : Integrable fr cuadrado := areaIntegrable (cu.mul (cr.comp continuous_fst))
  have id : Integrable fd cuadrado := areaIntegrable (cu.mul (cd.comp (continuous_fst.sub continuous_snd)))
  have ia : Integrable fa cuadrado := areaIntegrable (cu.mul (ca.comp (continuous_fst.add continuous_snd)))
  have e : (∫ z,U z*sumaLevantada false r d a z ∂cuadrado)=
      (∫ z,fr z ∂cuadrado)+(∫ z,fd z ∂cuadrado)+(∫ z,fa z ∂cuadrado) := by
    rw [←integral_add ir id]
    have irid : Integrable (fun z=>fr z+fd z) cuadrado := ir.add id
    rw [←integral_add irid ia]
    apply integral_congr_ae; filter_upwards with z
    dsimp [fr,fd,fa,sumaLevantada,transversal]; ring
  exact e.trans (congrArg₂ (·+·) (congrArg₂ (·+·) (adjuncion_de_fila_extendida U r cu cr)
    (adjuncion_de_diagonal_extendida U d cu cd false)) (adjuncion_de_diagonal_extendida U a cu ca true))

theorem pareja_diagonal_con_residual {U : ℝ×ℝ→ℝ} {w extra : ℝ→ℝ} {coef Z l r : ℝ} (i : Fin 3)
    (uc : Continuous U) (wc : Continuous w) (ec : Continuous extra)
    (long : r-l=2) (cap : ∀ t∈Icc l r,|cargaDeFranja U i t+extra t|≤Z) :
    let μ:=volume.restrict (Icc l r)
    2*coef*((∫ t,cargaDeFranja U i t*w t ∂μ)+(∫ t,extra t*w t ∂μ))≤
      2*Z^2+coef^2*(∫ t,w t^2 ∂μ) := by
  intro μ
  have fi:=carga_integrable_con_prueba uc wc i l r
  have ei : Integrable (fun t=>extra t*w t) μ := (ec.mul wc).continuousOn.integrableOn_Icc
  have wi : Integrable (fun t=>w t^2) μ := (wc.pow 2).continuousOn.integrableOn_Icc
  have zz : Integrable (fun _ : ℝ=>Z^2) μ := continuousOn_const.integrableOn_Icc
  have comp:=integral_mono_ae ((fi.add ei).const_mul (2*coef)) (zz.add (wi.const_mul (coef^2))) (by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Icc (a:=l) (b:=r))] with t ht
    simp only [Pi.add_apply]
    have hh:=sq_le_sq' (abs_le.mp (cap t ht)).1 (abs_le.mp (cap t ht)).2
    nlinarith only [sq_nonneg (cargaDeFranja U i t+extra t-coef*w t),hh])
  have tot : (∫ _ : ℝ,Z^2 ∂μ)=2*Z^2 := by
    simp [μ,integral_const,Real.volume_Icc,long,Measure.real]
  simp only [Pi.add_apply] at comp
  rw [integral_const_mul,integral_add fi ei,integral_add zz (wi.const_mul _),integral_const_mul,tot] at comp
  exact comp
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.trabajo_por_las_tres_proyecciones
#print axioms ArticuloA.Historias.pareja_diagonal_con_residual
