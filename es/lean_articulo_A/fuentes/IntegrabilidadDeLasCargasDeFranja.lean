import ProyeccionFisicaEnLaFranja
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
theorem carga_de_franja_medible {U : ℝ×ℝ→ℝ} (um : Measurable U) (i : Fin 3) :
    Measurable (cargaDeFranja U i) := by
  have mc : Measurable (fun w : ℝ×ℝ=>columnaEnFibra i w.1 w.2) := by
    fin_cases i <;> simp [columnaEnFibra] <;> fun_prop
  have mh : Measurable (Function.uncurry (enLaFranja U i)) := Measurable.ite
    (measurableSet_Icc.preimage mc) (um.comp (measurable_snd.prodMk mc)) measurable_const
  let μ:=volume.restrict (Ioc (0:ℝ) 1)
  have eq : cargaDeFranja U i=fun s=>∫ r,enLaFranja U i s r ∂μ := by
    funext s; exact intervalIntegral.integral_of_le zero_le_one
  rw [eq]; exact (mh.stronglyMeasurable.integral_prod_right (ν:=μ)).measurable

theorem carga_acotada_en_cualquier_etiqueta {U : ℝ×ℝ→ℝ} (uc : Continuous U) (i : Fin 3) :
    ∃ B : ℝ,∀ s,‖cargaDeFranja U i s‖≤B := by
  obtain ⟨B,hB⟩:=(isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (K:=unidadCerrada ×ˢ unidadCerrada) uc.norm.continuousOn
  have bp:0≤B := (norm_nonneg _).trans (hB (mem_image_of_mem _ (show ((0:ℝ),(0:ℝ))∈unidadCerrada ×ˢ unidadCerrada from
    ⟨⟨le_rfl,zero_le_one⟩,⟨le_rfl,zero_le_one⟩⟩)))
  refine ⟨B,fun s=>?_⟩
  have enc : ∀ r∈uIoc (0:ℝ) 1,‖enLaFranja U i s r‖≤B := by
    intro r hr; rw [uIoc_of_le zero_le_one] at hr
    unfold enLaFranja; split_ifs with hc
    · exact hB (mem_image_of_mem _ ⟨⟨hr.1.le,hr.2⟩,hc⟩)
    · simpa using bp
  simpa only [cargaDeFranja,sub_zero,abs_one,mul_one] using
    (intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=1) (f:=enLaFranja U i s) enc)

theorem carga_integrable_con_prueba {U : ℝ×ℝ→ℝ} {w : ℝ→ℝ} (uc : Continuous U) (wc : Continuous w)
    (i : Fin 3) (l r : ℝ) :
    Integrable (fun s=>cargaDeFranja U i s*w s) (volume.restrict (Icc l r)) := by
  exact wc.continuousOn.integrableOn_Icc.bdd_mul (carga_de_franja_medible uc.measurable i).aestronglyMeasurable
    (carga_acotada_en_cualquier_etiqueta uc i)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.carga_de_franja_medible
#print axioms ArticuloA.Historias.carga_acotada_en_cualquier_etiqueta
#print axioms ArticuloA.Historias.carga_integrable_con_prueba
