import OscilacionDeUnaCuerdaMedible
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

open scoped Topology
theorem cavidad_continua_para_campos_medibles (f : Fin 4→ℝ→ℝ) (fi : ∀ i,Integrable (f i))
    (fm : ∀ i,Measurable (f i)) (M : ℝ) (cap : ∀ i y,|f i y|≤M) (i : Fin 4) :
    ContinuousOn (cavidadFisica f i) (rangoF i) := by
  let V (j : Fin 3) (s : ℝ):=traslacionEnL1 (fi (familiaTransversal i j)) (coord (familiaTransversal i j) (puntoDeCuerda i s 0))
  have vc j : Continuous (V j) := by
    apply (traslacion_en_L1_continua _).comp
    have zz : Continuous (fun s=>puntoDeCuerda i s 0) := by fin_cases i <;> dsimp [puntoDeCuerda] <;> fun_prop
    have co (g : Fin 4) : Continuous (coord g) := by
      fin_cases g; exacts [continuous_fst,continuous_snd,continuous_fst.sub continuous_snd,continuous_fst.add continuous_snd]
    exact (co _).comp zz
  have lc : Continuous (longitudDeCuerda i) := by
    unfold longitudDeCuerda; fin_cases i <;> simp [desplazamientoOblicuo] <;> fun_prop
  intro v _
  let B (s : ℝ):= M^2*(∑ j : Fin 3,(abs (pendienteTransversal i j)⁻¹)*dist (V j s) (V j v))+
    M^3*|longitudDeCuerda i s-longitudDeCuerda i v|
  have c : Continuous B := (continuous_const.mul
    (continuous_finset_sum _ (fun j _=>continuous_const.mul ((vc j).dist continuous_const)))).add
    (continuous_const.mul (lc.sub continuous_const).abs)
  have z : B v=0 := by simp [B]
  have tend : Tendsto B (𝓝[rangoF i] v) (𝓝 0) := z ▸ c.continuousAt.continuousWithinAt
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) _ tend
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact oscilacion_de_cavidad_medible f fi fm M cap i (v:=v) hs

theorem representante_por_la_cavidad {f : Fin 4→ℝ→ℝ} (fi : ∀ i,Integrable (f i))
    (fm : ∀ i,Measurable (f i)) (M : ℝ) (cap : ∀ i y,|f i y|≤M)
    (nn : ∀ i y,0≤f i y) {a : ℝ} (ap : 0<a) (i : Fin 4) :
    let q:=fun s=>1/(1+a*cavidadFisica f i s)
    ContinuousOn q (rangoF i) ∧ ∀ s∈rangoF i,0<q s ∧ q s≤1 := by
  have den s (hs : s∈rangoF i) : 1≤1+a*cavidadFisica f i s := by
    have v : 0≤cavidadFisica f i s := by
      apply intervalIntegral.integral_nonneg (longitud_en_unidad i hs).1
      intro t _
      exact mul_nonneg (mul_nonneg (nn _ _) (nn _ _)) (nn _ _)
    exact le_add_of_nonneg_right (mul_nonneg ap.le v)
  have hi := cavidad_continua_para_campos_medibles f fi fm M cap i
  exact ⟨continuousOn_const.div (continuousOn_const.add (continuousOn_const.mul hi))
    (fun s hs=>(zero_lt_one.trans_le (den s hs)).ne'),fun s hs=>⟨one_div_pos.mpr (zero_lt_one.trans_le (den s hs)),
    (div_le_one (zero_lt_one.trans_le (den s hs))).mpr (den s hs)⟩⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cavidad_continua_para_campos_medibles
#print axioms ArticuloA.Historias.representante_por_la_cavidad
