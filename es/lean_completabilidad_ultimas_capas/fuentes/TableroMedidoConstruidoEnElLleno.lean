import LimiteDeLasMedidasConDensidad
import LimitesDeOcupacionYLeyDeEuler
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
theorem tablero_medido_desde_el_limite {P : ℕ→TableroMedido} {p : ℕ→FactoresContinuos} {b : ℕ→ℝ}
    {x : ℕ→ℝ≥0} {p₀ : FactoresContinuos} {b₀ κ M L : ℝ} (bp : 0<b₀) (kp : 0<κ)
    (eq : ∀ j,EulerFisica (P j) (p j) (x j) (b j)) (sp : ∀ j,ControlEspacial (p j) κ M L)
    (bl : Tendsto b atTop (𝓝 b₀)) (zx : Tendsto (fun j=>(x j:ℝ)) atTop (𝓝 0))
    (cp : ∀ i,Continuous (camposFisicos p₀ i))
    (lc : ∀ i,∀ s∈rangoF i,Tendsto (fun j=>camposFisicos (p j) i s) atTop (𝓝 (camposFisicos p₀ i s))) :
    ∃ P₀ : TableroMedido,EulerFisica P₀ p₀ 0 b₀ := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance
  let ν:=densidadDelExtremo p₀ b₀
  let m:=ocupacionDelExtremo p₀
  have nv : Measurable ν := (producto_continuo_en_el_plano cp b₀).measurable.real_toNNReal
  have mv (i : Fin 4) : Measurable (m i) := (show Continuous (fun s=>1-holguraLinea p₀ 0 i s) from
    continuous_const.sub (continuous_const.mul (cp i))).measurable.real_toNNReal
  have lv:=densidad_limite_del_producto bp eq bl lc
  have occ i:=ocupacion_limite_sin_truncar eq zx lc i
  have lm i : ∀ᵐ s ∂marginalRef i,Tendsto (fun j=>((P j).m i s:ℝ)) atTop (𝓝 (m i s:ℝ)) :=
    (occ i).mono (fun s hs=> hs.2.symm ▸ hs.1)
  let B:=(1/κ^4)*M^4
  have cap j : ∀ᵐ z ∂cuadrado,((P j).ν z:ℝ)≤B := by
    filter_upwards [tablero_en_dominio,(eq j).real] with z hz hh
    rw [hh]
    have prod:=limites_del_producto (sp j) kp.le _ _ hz.1 hz.2
    exact mul_le_mul (techo_desde_la_masa (eq j) (sp j) kp) prod.2 (by unfold pesoContinuo; positivity) (by positivity)
  have law : LeyMarginal ν m := ley_de_imagen_cerrada_en_el_limite nv mv cap lv lm
  have intg : Integrable (fun z=>(ν z:ℝ)) cuadrado := by
    apply (integrable_const (μ:=cuadrado) B).mono' nv.coe_nnreal_real.aestronglyMeasurable
    filter_upwards [lv,ae_all_iff.mpr cap] with z l bounds
    simpa using le_of_tendsto l (Eventually.of_forall (bounds ·))
  have admiss i : ∀ᵐ s ∂marginalRef i,(m i s:ℝ)≤1 := by
    filter_upwards [lm i,ae_all_iff.mpr (fun j=>(P j).admisible i)] with s l bounds
    exact le_of_tendsto l (Eventually.of_forall (bounds ·))
  let full : TableroMedido:=⟨ν,m,law,intg,admiss⟩
  refine ⟨full,bp,?_,?_,?_⟩
  · have mass:=masa_de_cada_linea law 0
    have one s : (m 0 s:ℝ)=1 := by simp [m,ocupacionDelExtremo,holguraLinea]
    have ref : marginalRef 0=unidad := Measure.restrict_congr_set Ioc_ae_eq_Icc
    change masaDensidad ν=1-((0:ℝ≥0):ℝ)
    simpa [one,ref] using mass.symm
  · exact Eventually.of_forall (fun z=>Real.coe_toNNReal _ (by unfold pesoContinuo; positivity))
  · intro i
    filter_upwards [occ i] with s hs
    change 1-(ocupacionDelExtremo p₀ i s:ℝ)=holguraLinea p₀ 0 i s
    rw [hs.2]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tablero_medido_desde_el_limite
