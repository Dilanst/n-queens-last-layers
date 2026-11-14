import DesintegracionDelTableroBorelAcotado
import AdjuncionDeLaDensidadTrasladada
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Classical
theorem adjuncion_de_fila_borel (U : ℝ×ℝ→ℝ) (w : ℝ→ℝ) (um : Measurable U) (wm : Measurable w)
    {D M : ℝ} (ub : ∀ z,‖U z‖≤D) (wb : ∀ s,‖w s‖≤M) :
    (∫ z,U z*w z.1 ∂cuadrado)=∫ r,(∫ c in (0:ℝ)..1,U (r,c))*w r ∂unidad := by
  have fi : Integrable (fun z : ℝ×ℝ=>U z*w z.1) cuadrado := by
    letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
    letI : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance
    apply (integrable_const (D*M)).mono' ((um.mul (wm.comp measurable_fst)).aestronglyMeasurable)
    filter_upwards with z
    rw [norm_mul]; exact mul_le_mul (ub z) (wb _) (norm_nonneg _) ((norm_nonneg _).trans (ub z))
  rw [cuadrado,integral_prod _ fi]
  apply integral_congr_ae; filter_upwards with r
  change (∫ c in Icc (0:ℝ) 1,U (r,c)*w r)=_
  rw [integral_mul_const,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one]

private theorem fiber_test (U : ℝ×ℝ→ℝ) (w : ℝ→ℝ) (a : Bool) (d : ℝ) :
    (∫ r in Icc (0:ℝ) 1,if d∈ventana r then
      U (r,colOblicua a r d)*w (coord (indiceDeLaSeccion a) (r,colOblicua a r d)) else 0)=
      cargaDeFranja U (if a then 2 else 1) (ordenadaFisica a d)*w (ordenadaFisica a d) := by
  unfold cargaDeFranja; rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,←integral_mul_const]
  apply setIntegral_congr_fun measurableSet_Icc; intro r _
  cases a
  · have iff : r-d∈unidadCerrada ↔ d∈ventana r := by
      change (0≤r-d ∧ r-d≤1) ↔ r-1≤d ∧ d≤r
      constructor <;> rintro ⟨l,h⟩ <;> constructor <;> linarith
    by_cases h : d∈ventana r <;> simp [enLaFranja,columnaEnFibra,colOblicua,coord,indiceDeLaSeccion,ordenadaFisica,iff,h]
  · have iff : d+1-r∈unidadCerrada ↔ d∈ventana r := by
      change (0≤d+1-r ∧ d+1-r≤1) ↔ r-1≤d ∧ d≤r
      constructor <;> rintro ⟨l,h⟩ <;> constructor <;> linarith
    by_cases h : d∈ventana r <;> simp [enLaFranja,columnaEnFibra,colOblicua,coord,indiceDeLaSeccion,ordenadaFisica,
      show 1-(r-d)=d+1-r by ring,iff,h]

theorem adjuncion_de_diagonal_borel (U : ℝ×ℝ→ℝ) (w : ℝ→ℝ) (um : Measurable U) (wm : Measurable w)
    {D M : ℝ} (ub : ∀ z,‖U z‖≤D) (wb : ∀ s,‖w s‖≤M) (a : Bool) :
    (∫ z,U z*w (coord (indiceDeLaSeccion a) z) ∂cuadrado)=
      ∫ s,cargaDeFranja U (if a then 2 else 1) s*w s ∂(if a then anti else diag) := by
  have fc : Measurable (fun z : ℝ×ℝ=>U z*w (coord (indiceDeLaSeccion a) z)) :=
    um.mul (wm.comp (coord_medible _))
  have bd z : ‖U z*w (coord (indiceDeLaSeccion a) z)‖≤D*M := by
    rw [norm_mul]; exact mul_le_mul (ub z) (wb _) (norm_nonneg _) ((norm_nonneg _).trans (ub z))
  rw [desintegrar_tablero_borel_acotado a fc bd]
  simp_rw [fiber_test U w a]
  cases a
  · rfl
  · change (∫ d in Icc (-1:ℝ) 1,cargaDeFranja U 2 (d+1)*w (d+1))=∫ s in Icc (0:ℝ) 2,cargaDeFranja U 2 s*w s
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
    let f:=fun s=>cargaDeFranja U 2 s*w s
    change (∫ d in (-1:ℝ)..1,f (d+1))=∫ s in Icc (0:ℝ) 2,f s
    rw [intervalIntegral.integral_comp_add_right,integral_Icc_eq_integral_Ioc]
    norm_num [intervalIntegral.integral_of_le]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.adjuncion_de_fila_borel
#print axioms ArticuloA.Historias.adjuncion_de_diagonal_borel
