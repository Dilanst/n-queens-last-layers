import PromedioDeLosCrucesPorDobleCuenta
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical

/-- Uniform-layer probability of a configuration with an empty cross below the indicated threshold. -/
def probabilidadDeCruceEscaso (n h : ℕ) (t : ℝ) := ∑ Q∈nivel n (n-h),
  if ∃ z∈cruces Q,(crossDegree (n-h) Q z:ℝ)<t*(n:ℝ) then (count n (n-h):ℝ)⁻¹ else 0

theorem reparacion_tipica_en_cada_cruce {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0))) :
    ∃ t : ℝ,0<t ∧ ∀ h : ℕ,0<h →
      Tendsto (fun n=>probabilidadDeCruceEscaso n h t) atTop (𝓝 0) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  let t:=b 0*κ^8/2
  have mp : 0<b 0*κ^8:=mul_pos (rama.euler 0 zero).coef (pow_pos rama.kp _)
  have tp : 0<t:=half_pos mp
  refine ⟨t,tp,?_⟩
  intro h hh
  have dir:=(directa_del_articulo rama (euler_puntual_de_la_rama rama) cont first h hh).1 t tp
  apply squeeze_zero' _ _ dir
  · apply Eventually.of_forall; intro n; unfold probabilidadDeCruceEscaso
    apply Finset.sum_nonneg; intro Q _; split <;> positivity
  · filter_upwards [eventually_gt_atTop 0] with n np
    have npos : (0:ℝ)<n:=by exact_mod_cast np
    unfold probabilidadDeCruceEscaso probCruceMalo
    apply Finset.sum_le_sum; intro Q _
    split_ifs with scarce bad bad
    · exact le_rfl
    · exfalso; obtain ⟨z,hz,small⟩:=scarce
      have floor : b 0*κ^8≤aDelLleno p b z := piso_integral_del_cruce (rama.espacio 0 zero)
        rama.kp rama.lp (rama.euler 0 zero).coef (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
      have small' := (div_lt_iff₀ npos).mpr small
      apply bad; refine ⟨z,hz,?_⟩
      have less : (crossDegree (n-h) Q z:ℝ)/n < aDelLleno p b z-t := by dsimp [t] at small' ⊢; linarith
      exact lt_of_lt_of_le (by linarith only [less] : t < -((crossDegree (n-h) Q z:ℝ)/n-aDelLleno p b z)) (neg_le_abs _)
    · positivity
    · exact le_rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reparacion_tipica_en_cada_cruce
