import ConvexidadFuerteDelPotencialDeHolgura
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped Topology
/-- El espacio puede ser el subtipo de la caja cerrada. El punto medio solo se usa
para comparar el defecto del funcional con la distancia entre dos competidores. -/
theorem minimo_unico_por_brecha_de_punto_medio {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (J : X→ℝ) (medio : X→X→X) (jc : Continuous J) (lower : BddBelow (range J))
    {K : ℝ} (kp : 0<K)
    (gap : ∀ u v,dist u v^2 ≤ K*((J u+J v)/2-J (medio u v))) :
    ∃! u,∀ v,J u≤J v := by
  classical
  let d:=sInf (range J)
  have low v : d≤J v := csInf_le lower (mem_range_self v)
  obtain ⟨a,_,ta,mem⟩:=exists_seq_tendsto_sInf (range_nonempty J) lower
  choose y hy using mem
  have cauchy : CauchySeq y := by
    apply Metric.cauchySeq_iff.mpr
    intro ε ep
    have above : ∀ᶠ j in atTop,a j<d+ε^2/K :=
      ta.eventually_lt_const (lt_add_of_pos_right _ (div_pos (sq_pos_of_pos ep) kp))
    obtain ⟨N,hN⟩:=eventually_atTop.1 above
    refine ⟨N,fun i hi j hj=>?_⟩
    have g:=gap (y i) (y j)
    have v1:=hN i hi; have v2:=hN j hj
    rw [hy i,hy j] at g
    have b : (a i+a j)/2-J (medio (y i) (y j))<ε^2/K := by linarith [low (medio (y i) (y j))]
    have b2:=(lt_div_iff₀ kp).mp b
    rw [mul_comm] at b2
    nlinarith [(dist_nonneg : 0≤dist (y i) (y j))]
  obtain ⟨z,tz⟩:=cauchySeq_tendsto_of_complete cauchy
  have lim : Tendsto (fun i=>J (y i)) atTop (𝓝 d) := by simpa only [hy] using ta
  have val : J z=d := tendsto_nhds_unique (jc.continuousAt.tendsto.comp tz) lim
  refine ⟨z,fun v=>val ▸ low v,?_⟩
  intro v hv
  have w:=hv z
  have eq : J v=d := le_antisymm (w.trans val.le) (low v)
  have g:=gap v z
  rw [eq,val] at g
  have nz:=(low (medio v z))
  apply dist_eq_zero.mp
  nlinarith [mul_nonpos_of_nonneg_of_nonpos kp.le (show (d+d)/2-J (medio v z)≤0 by linarith),(dist_nonneg : 0≤dist v z)]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.minimo_unico_por_brecha_de_punto_medio
