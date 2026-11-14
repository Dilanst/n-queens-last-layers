import MarginalesDesdeElTableroSinLipschitz
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology ENNReal
/-- Continuity on a single Borel event. A bound is needed only on the fixed
    reference measure, and each member may have a different null exceptional set. -/
theorem limite_de_masa_en_un_conjunto {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {u : ℕ→α→ℝ≥0} {v : α→ℝ≥0} {B : ℝ}
    (mu : ∀ j,Measurable (u j)) (mv : Measurable v) (bu : ∀ j,∀ᵐ z ∂μ,(u j z:ℝ)≤B)
    (lim : ∀ᵐ z ∂μ,Tendsto (fun j=>(u j z:ℝ)) atTop (𝓝 (v z:ℝ))) (E : Set α) (em : MeasurableSet E) :
    Tendsto (fun j=>(μ.withDensity (fun z=>(u j z:ℝ≥0∞))) E) atTop
      (𝓝 ((μ.withDensity (fun z=>(v z:ℝ≥0∞))) E)) := by
  let η:=μ.restrict E
  have bm j : ∀ᵐ z ∂η,‖(u j z:ℝ)‖≤B := (ae_restrict_of_ae (bu j)).mono (fun z hz=>by simpa using hz)
  have lv : ∀ᵐ z ∂η,Tendsto (fun j=>(u j z:ℝ)) atTop (𝓝 (v z:ℝ)) := ae_restrict_of_ae lim
  have bi : Integrable (fun _ : α=>B) η := integrable_const _
  have ui j : Integrable (fun z=>(u j z:ℝ)) η :=
    bi.mono' (NNReal.continuous_coe.measurable.comp (mu j)).aestronglyMeasurable (bm j)
  have vi : Integrable (fun z=>(v z:ℝ)) η := by
    apply bi.mono' (NNReal.continuous_coe.measurable.comp mv).aestronglyMeasurable
    filter_upwards [lv,ae_all_iff.mpr bm] with z l bounds
    simpa using le_of_tendsto l (Eventually.of_forall (fun j=>by simpa using bounds j))
  have integralLimit:=tendsto_integral_of_dominated_convergence (μ:=η) (fun _=>B)
    (fun j=>(NNReal.continuous_coe.measurable.comp (mu j)).aestronglyMeasurable) bi bm lv
  have lift:=ENNReal.continuous_ofReal.continuousAt.tendsto.comp integralLimit
  simpa only [withDensity_apply _ em,lintegral_coe_eq_integral _ (ui _),lintegral_coe_eq_integral _ vi,Function.comp_def,η] using lift

theorem ley_de_imagen_cerrada_en_el_limite {P : ℕ→TableroMedido} {ν : ℝ×ℝ→ℝ≥0} {m : Fin 4→ℝ→ℝ≥0} {B : ℝ}
    (nv : Measurable ν) (mv : ∀ i,Measurable (m i))
    (cap : ∀ j,∀ᵐ z ∂cuadrado,((P j).ν z:ℝ)≤B)
    (lv : ∀ᵐ z ∂cuadrado,Tendsto (fun j=>((P j).ν z:ℝ)) atTop (𝓝 (ν z:ℝ)))
    (lm : ∀ i,∀ᵐ s ∂marginalRef i,Tendsto (fun j=>((P j).m i s:ℝ)) atTop (𝓝 (m i s:ℝ))) : LeyMarginal ν m := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance
  refine ⟨nv,mv,?_⟩
  intro i
  ext E em
  rw [Measure.map_apply (coord_medible i) em]
  have l:=limite_de_masa_en_un_conjunto cuadrado (fun j=>(P j).ley.densidad) nv cap lv _ ((coord_medible i) em)
  have r:=limite_de_masa_en_un_conjunto (marginalRef i) (fun j=>(P j).ley.densidadLinea i) (mv i)
    (fun j=>(P j).admisible i) (lm i) E em
  have eq j := congrArg (fun μ : Measure ℝ=>μ E) ((P j).ley.imagen i)
  simp only [Measure.map_apply (coord_medible i) em] at eq
  exact tendsto_nhds_unique l (r.congr (fun j=>(eq j).symm))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.limite_de_masa_en_un_conjunto
#print axioms ArticuloA.Historias.ley_de_imagen_cerrada_en_el_limite
