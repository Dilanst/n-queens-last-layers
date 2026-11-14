import SeccionDeUnaDiagonal
open Set MeasureTheory Filter
open scoped Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

def parametroOblicuo (anti : Bool) (r c : ℝ) := if anti then r+c-1 else r-c

private theorem recorte_en_fila (anti : Bool) (H : ℝ→ℝ) {r : ℝ} (hr : r∈Icc 0 1) :
    (∫ c in (0:ℝ)..1,H (parametroOblicuo anti r c)) =
      ∫ d in Icc (-1:ℝ) 1,if d∈ventana r then H d else 0 := by
  have sub : Icc (r-1) r⊆Icc (-1:ℝ) 1 := fun _ ht => ⟨by linarith [hr.1,ht.1],ht.2.trans hr.2⟩
  change _=∫ d in Icc (-1:ℝ) 1,(Icc (r-1) r).indicator H d
  rw [recorte_de_intervalos (by linarith) sub]
  cases anti
  · simp [parametroOblicuo,intervalIntegral.integral_comp_sub_left]
  · have eq : (fun c => H (parametroOblicuo true r c))=fun c => H (c+(r-1)) := by
      funext c; congr 1; simp [parametroOblicuo]; ring
    rw [eq,intervalIntegral.integral_comp_add_right]; congr 1 <;> ring

/-- Joint integration in centered diagonal coordinate and row, with the square
cut out exactly by r-1 ≤ d ≤ r. The restricted product has no Jacobian factor. -/
theorem desintegrar_el_tablero (anti : Bool) {F : ℝ×ℝ→ℝ} (fc : Continuous F) :
    (∫ z,F z ∂cuadrado)=∫ d in Icc (-1:ℝ) 1,∫ r in Icc (0:ℝ) 1,
      if d∈ventana r then F (r,colOblicua anti r d) else 0 := by
  let U:=Icc (0:ℝ) 1
  let D:=Icc (-1:ℝ) 1
  let μ : Measure ℝ:=volume.restrict U
  let ν : Measure ℝ:=volume.restrict D
  letI : IsFiniteMeasure μ:=⟨by simp [μ,U,Real.volume_Icc]⟩
  letI : IsFiniteMeasure ν:=⟨by simp [ν,D,Real.volume_Icc]⟩
  let H:=fun r d => F (r,colOblicua anti r d)
  let V: Set (ℝ×ℝ):={z | z.2∈ventana z.1}
  have Vm : MeasurableSet V := (measurableSet_le (measurable_fst.sub measurable_const) measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst)
  have hc : Continuous (Function.uncurry H) := by
    apply fc.comp; cases anti <;> dsimp [colOblicua] <;> fun_prop
  have fi : Integrable F (μ.prod μ) := by
    rw [show μ=volume.restrict U from rfl,Measure.prod_restrict]
    exact fc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hi : Integrable (Function.uncurry H) (μ.prod ν) := by
    rw [show μ=volume.restrict U from rfl,show ν=volume.restrict D from rfl,Measure.prod_restrict]
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have both := hi.indicator Vm
  change Integrable (Function.uncurry (fun r d => if d∈ventana r then H r d else 0)) (μ.prod ν) at both
  change (∫ z,F z ∂(μ.prod μ))=_
  rw [integral_prod _ fi]
  apply Eq.trans _ (integral_integral_swap both)
  apply setIntegral_congr_fun measurableSet_Icc; intro r hr
  change (∫ c in Icc (0:ℝ) 1,F (r,c))=_
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
  apply Eq.trans _ (recorte_en_fila anti (H r) hr)
  apply intervalIntegral.integral_congr; intro c _
  change F (r,c)=F (r,colOblicua anti r (parametroOblicuo anti r c))
  have eq : colOblicua anti r (parametroOblicuo anti r c)=c := by
    cases anti
    · simp [colOblicua,parametroOblicuo]
    · simp [colOblicua,parametroOblicuo]; ring
  rw [eq]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.desintegrar_el_tablero
