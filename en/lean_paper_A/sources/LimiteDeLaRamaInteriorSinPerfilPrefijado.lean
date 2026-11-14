import R15ParaLaRamaCompleta
import ConstruccionDelRepresentanteContinuoDelLleno
import EntradasDelArticuloDesdeLasMasas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology Uniformity
/-- A possibly nonsequential approach to full mass through the physical interior. -/
theorem limite_uniforme_de_la_rama_interior {ι : Type*} (l : Filter ι) [NeBot l]
    {P : ι→TableroMedido} {p : ι→FactoresContinuos} {b : ι→ℝ} {x : ι→ℝ≥0}
    {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ j,EulerFisica (P j) (p j) (x j) (b j)) (sp : ∀ j,ControlEspacial (p j) κ M L)
    (xp : ∀ j,0<x j) (half : ∀ j,(x j:ℝ)≤1/2) (zero : Tendsto (fun j=>(x j:ℝ)) l (𝓝 0)) :
    ∃ b₀ : ℝ,0<b₀ ∧ Tendsto b l (𝓝 b₀) ∧
      ∃ f₀ : Fin 4→ℝ→ℝ,∀ i,ContinuousOn (f₀ i) (rangoF i) ∧
        TendstoUniformlyOn (fun j=>camposFisicos (p j) i) (f₀ i) l (rangoF i) := by
  have ca : ∀ u : ℝ,0<u → ∀ᶠ mn : ι×ι in l ×ˢ l,
      |(x mn.2:ℝ)-x mn.1|≤u ∧ |b mn.2-b mn.1|≤u ∧
      (∑ g,masaExterior (fun j y=>|camposFisicos (p mn.1) j y-camposFisicos (p mn.2) j y|) g)≤u := by
    intro u up
    obtain ⟨d,dp,step⟩:=criterio_R15_entre_parametros kp k1 m1 lp up
    have sm : ∀ᶠ j in l,(x j:ℝ)<min u d := (tendsto_order.mp zero).2 _ (lt_min up dp)
    filter_upwards [sm.prod_mk sm] with a ha
    have sub : |(x a.2:ℝ)-x a.1|<min u d := abs_lt.mpr
      ⟨by linarith only [ha.1,(x a.2).coe_nonneg],by linarith only [ha.2,(x a.1).coe_nonneg]⟩
    obtain ⟨db,dm⟩:=step (eq a.1) (eq a.2) (sp a.1) (sp a.2)
      (normalizacion_R15_en_masa_interior (eq a.1) (xp a.1)) (normalizacion_R15_en_masa_interior (eq a.2) (xp a.2))
      (half a.1) (half a.2) (sub.trans_le (min_le_right ..))
    exact ⟨sub.le.trans (min_le_left ..),(abs_sub_comm _ _).le.trans db,dm⟩
  have uc : UniformCauchySeqOn (fun j (_ : Unit)=>b j) l univ := by
    intro v hv
    obtain ⟨ε,ep,vin⟩:=Metric.mem_uniformity_dist.mp hv
    filter_upwards [ca (ε/2) (half_pos ep)] with a ha
    intro t _
    apply vin
    rw [Real.dist_eq,abs_sub_comm]
    exact ha.2.1.trans_lt (half_lt_self ep)
  have cb : Cauchy (map b l) := uc.cauchy_map (x:=()) (mem_univ _)
  have bl : Tendsto b l (𝓝 (lim (map b l))) := cb.le_nhds_lim
  have lb : (1/2:ℝ)/M^4 ≤ lim (map b l) :=
    ge_of_tendsto bl (Eventually.of_forall (fun j=>(banda_del_normalizador (eq j) (sp j) kp m1 (half j)).1))
  have minpos : 0<(1/2:ℝ)/M^4 := div_pos (by norm_num) (pow_pos (zero_lt_one.trans_le m1) 4)
  refine ⟨_,minpos.trans_le lb,bl,?_⟩
  apply representante_continuo_desde_cauchy_de_la_rama l p x b (zero_le_one.trans m1)
    (show 0≤1/κ^4 by positivity) (fun j i=>continua_de_cota lp (regular_familia (sp j) i).oscilacion) _ _ _ ca
  · intro j i s hs
    have h:=(banda_de_campo (sp j) i s).2
    simpa only [campoR15,camposFisicos,recorte_fijo i hs,abs_of_nonneg (NNReal.coe_nonneg _)] using h
  · intro j
    rw [abs_of_pos (eq j).coef]
    exact techo_desde_la_masa (eq j) (sp j) kp
  · intro j i
    filter_upwards [linea_en_dominio i] with t ht
    fin_cases i
    · exact integral_euler_en_rectas (eq j) (sp j) lp 0 (by decide) t ht
    · exact integral_euler_en_rectas (eq j) (sp j) lp 1 (by decide) t ht
    · exact euler_oblicua_puntual (eq j) (sp j) lp false t ht
    · exact euler_oblicua_puntual (eq j) (sp j) lp true t ht
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.limite_uniforme_de_la_rama_interior
