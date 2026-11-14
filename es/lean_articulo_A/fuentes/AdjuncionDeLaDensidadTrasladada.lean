import ProyeccionFisicaEnLaFranja
import PruebasContinuasParaLasOblicuas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
theorem adjuncion_de_fila_extendida (U : ℝ×ℝ→ℝ) (w : ℝ→ℝ) (uc : Continuous U) (wc : Continuous w) :
    (∫ z,U z*w z.1 ∂cuadrado)=∫ r,(∫ c in (0:ℝ)..1,U (r,c))*w r ∂unidad := by
  have fi : Integrable (fun z : ℝ×ℝ=>U z*w z.1) cuadrado := by
    rw [cuadrado,unidad,Measure.prod_restrict]
    exact (uc.mul (wc.comp continuous_fst)).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
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

theorem adjuncion_de_diagonal_extendida (U : ℝ×ℝ→ℝ) (w : ℝ→ℝ) (uc : Continuous U) (wc : Continuous w) (a : Bool) :
    (∫ z,U z*w (coord (indiceDeLaSeccion a) z) ∂cuadrado)=
      ∫ s,cargaDeFranja U (if a then 2 else 1) s*w s ∂(if a then anti else diag) := by
  have coordc : Continuous (coord (indiceDeLaSeccion a)) := by
    cases a; exacts [continuous_fst.sub continuous_snd,continuous_fst.add continuous_snd]
  have fc : Continuous (fun z : ℝ×ℝ=>U z*w (coord (indiceDeLaSeccion a) z)) := uc.mul (wc.comp coordc)
  rw [desintegrar_el_tablero a fc]
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
#print axioms ArticuloA.Historias.adjuncion_de_fila_extendida
#print axioms ArticuloA.Historias.adjuncion_de_diagonal_extendida
