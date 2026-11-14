import MediasGeometricasDeLosFactores
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem etiqueta_cumple_en_el_tablero (i : Fin 4) {S : Set ℝ} (ms : MeasurableSet S)
    (full : ∀ᵐ s ∂marginalRef i,s∈S) : ∀ᵐ z ∂cuadrado,coord i z∈S := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  have box : ∀ᵐ t ∂unidad,t∈Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have ref : marginalRef i=volume.restrict (rangoF i) := by
    have H : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [H]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have rect (j : Fin 4) (fj : ∀ᵐ s ∂marginalRef j,s∈S) (u : j.val<2) :
      ∀ᵐ s ∂unidad,s∈S := by
    have eq : marginalRef j=unidad := by
      rcases (show j=0 ∨ j=1 by omega) with rfl|rfl <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
    rwa [←eq]
  by_cases rc : i.val<2
  · have hi:=rect i full rc
    apply (Measure.ae_prod_iff_ae_ae (ms.preimage (coord_medible i))).mpr
    rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
    · exact hi.mono (fun _ h=>Eventually.of_forall (fun _=>h))
    · exact Eventually.of_forall (fun _=>hi)
  rw [ref] at full
  have base:=(ae_restrict_iff' measurableSet_Icc).mp full
  let Q (z : ℝ×ℝ):=coord i z.swap∈S
  have pull : ∀ᵐ z ∂unidad.prod unidad,Q z := by
    apply (Measure.ae_prod_iff_ae_ae (ms.preimage ((coord_medible i).comp measurable_swap))).mpr
    filter_upwards [box] with c hc
    let d:=if i=2 then -c else c
    have moved : ∀ᵐ r ∂volume,r+d∈rangoF i → r+d∈S :=
      (measurePreserving_add_right volume d).quasiMeasurePreserving.tendsto_ae.eventually base
    filter_upwards [box,ae_restrict_of_ae (s:=Icc (0:ℝ) 1) moved] with r hr good
    have hz:=coordenadas_en_dominio (z:=(r,c)) ⟨hr,hc⟩ i
    have id : coord i (r,c)=r+d := by
      rcases (show i=2 ∨ i=3 by omega) with rfl|rfl <;> simp [coord,d,sub_eq_add_neg]
    change coord i (r,c)∈S
    rw [id] at hz ⊢
    exact good hz
  have back:= (Measure.measurePreserving_swap (μ:=unidad) (ν:=unidad)).quasiMeasurePreserving.tendsto_ae.eventually pull
  exact back

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.etiqueta_cumple_en_el_tablero
