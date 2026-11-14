import IntegrandoDeLaReparacionDirecta
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

def sumaDeNumerador (n : ℕ) (p : FactoresContinuos) (r c : ℝ) :=
  ∑ e : Cell n,integrandoDirecto p r c (medio n e.1.val) (medio n e.2.val)

def perfilDirectoContinuo (p : FactoresContinuos) (b r c : ℝ) :=
  b*integralTablero (integrandoDirecto p r c)

theorem numerador_fisico_reescalado (n : ℕ) (p : FactoresContinuos) (r c : ℝ) :
    sumaDeNumerador n p r c=muestraTablero n (integrandoDirecto p r c) := by
  unfold sumaDeNumerador muestraTablero
  rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_range]; simp only [centro,nodo,zero_add,medio]

/-- The nonnegative mass of the mesh controls its numerator. Cancelling the mass
ratio avoids any loss from introducing a second lower bound on the denominator. -/
theorem error_del_cociente_de_cuadraturas {n q : ℕ} {p κ M L b}
    (np : 0<n) (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) (bp : 0<b)
    (masa : integralTablero (pesoContinuo p)=((q:ℝ)/n)/b)
    {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    |(q:ℝ)/n*(sumaDeNumerador n p r c/Wfisico n p)-perfilDirectoContinuo p b r c| ≤
      b*(2*(4*M^3*L)*M^4+2*(8*M^7*L))/(n:ℝ) := by
  let S:=sumaDeNumerador n p r c
  let W:=Wfisico n p
  let V:=integralTablero (integrandoDirecto p r c)
  let D:=integralTablero (pesoContinuo p)
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have mp : 0≤M := (NNReal.coe_nonneg _).trans (sp.Rmax _ hr)
  have wp : 0<W := (mul_pos (pow_pos kp 4) (pow_pos nr 2)).trans_le (masa_inferior sp kp.le)
  have cap : |S/W|≤M^4 := by
    rw [abs_div,abs_of_pos wp]
    apply (div_le_iff₀ wp).mpr
    unfold S sumaDeNumerador
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [mul_comm (M^4) W]
    change _ ≤ (∑ e : Cell n,pesoFisico n p e)*M^4
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum; intro e _
    unfold integrandoDirecto; rw [abs_mul,abs_of_nonneg (by unfold pesoContinuo; positivity : 0≤pesoContinuo p _ _)]
    exact mul_le_mul_of_nonneg_left (factor_acotado sp hr hc (medio_admisible e.1.isLt) (medio_admisible e.2.isLt))
      (by unfold pesoContinuo; positivity)
  have den : |(n:ℝ)^2*D-W|≤2*(4*M^3*L)*n := by
    rw [abs_sub_comm]; exact cuadratura_total_fisica np sp mp lp
  have num : |S-(n:ℝ)^2*V|≤2*(8*M^7*L)*n := by
    change |sumaDeNumerador n p r c-(n:ℝ)^2*V|≤_
    rw [abs_sub_comm,numerador_fisico_reescalado]
    exact cuadratura_del_integrando_directo sp kp.le lp hr hc n np
  have mass : (q:ℝ)/n=b*D := by rw [show D=((q:ℝ)/n)/b from masa]; field_simp; ring
  change |(q:ℝ)/n*(S/W)-b*V|≤_
  rw [mass]
  have eq : b*D*(S/W)-b*V=(b/(n:ℝ)^2)*(((n:ℝ)^2*D-W)*(S/W)+(S-(n:ℝ)^2*V)) := by
    field_simp [wp.ne',nr.ne']; ring
  rw [eq,abs_mul,abs_of_nonneg (div_nonneg bp.le (sq_nonneg _))]
  apply le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity))
  rw [abs_mul]
  apply le_trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul den cap (abs_nonneg _) (by positivity)) num)
    (by positivity))
  exact le_of_eq (by field_simp; ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_del_cociente_de_cuadraturas
