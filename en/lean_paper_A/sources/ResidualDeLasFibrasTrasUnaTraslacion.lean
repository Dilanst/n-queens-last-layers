import MonotoniaIntegralDelDualAnclado
import CuadraturaDelTablero
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical
open MeasureTheory Set Perfil
open scoped Interval
/-- Both strips have length |t|, even if the intervals are disjoint. -/
theorem error_de_las_dos_tiras (g : ℝ→ℝ) {B : ℝ} (bd : ∀ v,|g v|≤B)
    (mg : Measurable g) (t : ℝ) :
    |(∫ r in (0:ℝ)..1,g (r+t))-(∫ r in (0:ℝ)..1,g r)|≤2*B*|t| := by
  have ig (a b : ℝ) : IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff]
    have base : IntegrableOn (fun _ : ℝ => B) (uIoc a b) volume := integrableOn_const.mpr (Or.inr measure_Ioc_lt_top)
    apply base.mono' mg.aestronglyMeasurable
    exact Filter.Eventually.of_forall bd
  have add1:=intervalIntegral.integral_add_adjacent_intervals (ig 0 t) (ig t (1+t))
  have add2:=intervalIntegral.integral_add_adjacent_intervals (ig 0 1) (ig 1 (1+t))
  have bound (a b : ℝ) : |(∫ r in a..b,g r)|≤B*|b-a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=b) (f:=g) (fun x _ => bd x)
  rw [intervalIntegral.integral_comp_add_right,zero_add]
  have rearr : (∫ r in t..(1+t),g r)-(∫ r in (0:ℝ)..1,g r)=
      (∫ r in (1:ℝ)..(1+t),g r)-(∫ r in (0:ℝ)..t,g r) := by linarith only [add1,add2]
  rw [rearr]
  apply (abs_sub ..).trans
  have b1:=bound 1 (1+t)
  have b2:=bound 0 t
  rw [add_sub_cancel_left] at b1
  rw [sub_zero] at b2
  linarith only [b1,b2]

/-- Parametrise each fibre by r. Values outside the column interval are
zero. Original density is evaluated on the translated physical column or diagonal. -/
def columnaEnFibra (i : Fin 3) (v r : ℝ) := if i=0 then v else if i=1 then r-v else v-r
def etiquetaTrasladada (i : Fin 3) (v t : ℝ) := if i=0 then v else v+t
def enLaFranja (u : ℝ×ℝ→ℝ) (i : Fin 3) (v r : ℝ) :=
  if columnaEnFibra i v r∈unidadCerrada then u (r,columnaEnFibra i v r) else 0

theorem residual_de_fila_en_las_tres_fibras (u : ℝ×ℝ→ℝ) (um : Measurable u) {B : ℝ} (bp : 0≤B)
    (bd : ∀ r,∀ c∈unidadCerrada,|u (r,c)|≤B) (i : Fin 3) (v t : ℝ) :
    |(∫ r in (0:ℝ)..1,enLaFranja (fun z => u (z.1+t,z.2)) i v r)-
      (∫ r in (0:ℝ)..1,enLaFranja u i (etiquetaTrasladada i v t) r)|≤2*B*|t| := by
  let g:=enLaFranja u i (etiquetaTrasladada i v t)
  have coord (r : ℝ) : columnaEnFibra i (etiquetaTrasladada i v t) (r+t)=columnaEnFibra i v r := by
    fin_cases i <;> simp [columnaEnFibra,etiquetaTrasladada]
  have id : (fun r => enLaFranja (fun z => u (z.1+t,z.2)) i v r)=fun r => g (r+t) := by
    funext r; dsimp only [g,enLaFranja]; rw [coord]
  have cm : Measurable (columnaEnFibra i (etiquetaTrasladada i v t)) := by
    change Measurable (fun r => columnaEnFibra i (etiquetaTrasladada i v t) r)
    fin_cases i <;> simp [columnaEnFibra,etiquetaTrasladada] <;> fun_prop
  have meas : Measurable g := by
    dsimp [g,enLaFranja]
    apply Measurable.ite (measurableSet_Icc.preimage cm) (um.comp (measurable_id.prodMk cm)) measurable_const
  have cap (r) : |g r|≤B := by
    dsimp [g,enLaFranja]; split_ifs with hc
    · exact bd _ _ hc
    · simpa using bp
  rw [id]
  exact error_de_las_dos_tiras g cap meas t
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_las_dos_tiras
#print axioms ArticuloA.Historias.residual_de_fila_en_las_tres_fibras
