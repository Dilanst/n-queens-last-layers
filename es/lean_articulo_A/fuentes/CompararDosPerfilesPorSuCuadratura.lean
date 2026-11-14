import CambioDeLosFactoresEnElCruce
import CocienteDeCuadraturasDelCruce
open Filter
open scoped Topology BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

private theorem acotar_la_suma {n} (f : Cell n→ℝ) (d : ℝ) (cap : ∀ e,|f e|≤d) :
    |∑ e,f e|≤(n:ℝ)^2*d := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun e _ => cap e)).trans_eq
  simp [Fintype.card_prod,nsmul_eq_mul,pow_two,mul_assoc]

theorem error_integral_del_cruce {p κ M L b} (sp : ControlEspacial p κ M L) (kp : 0≤κ) (lp : 0≤L)
    (bp : 0≤b) (n : ℕ) (np : 0<n) {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    |perfilDirectoContinuo p b r c-b*sumaDeNumerador n p r c/(n:ℝ)^2|≤b*(16*M^7*L)/(n:ℝ) := by
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have est:=cuadratura_del_integrando_directo sp kp lp hr hc n np
  rw [←numerador_fisico_reescalado] at est
  unfold perfilDirectoContinuo
  rw [show b*integralTablero (integrandoDirecto p r c)-b*sumaDeNumerador n p r c/(n:ℝ)^2=
    (b/(n:ℝ)^2)*((n:ℝ)^2*integralTablero (integrandoDirecto p r c)-sumaDeNumerador n p r c) by
      field_simp; ring,abs_mul,abs_of_nonneg (by positivity : 0≤b/(n:ℝ)^2)]
  apply (mul_le_mul_of_nonneg_left est (by positivity)).trans_eq
  field_simp; ring

theorem comparar_dos_perfiles {p q κ M L b v d} (sp : ControlEspacial p κ M L)
    (sq : ControlEspacial q κ M L) (kp : 0≤κ) (lp : 0≤L) (bp : 0≤b) (vp : 0≤v)
    (close : CercaniaDeFactores p q d) {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    |perfilDirectoContinuo p b r c-perfilDirectoContinuo q v r c|≤b*(8*M^7*d)+M^8*|b-v| := by
  let W:=b*(8*M^7*d)+M^8*|b-v|
  let D:=(b+v)*(16*M^7*L)
  let A:=perfilDirectoContinuo p b r c
  let A':=perfilDirectoContinuo q v r c
  have est (n : ℕ) (np : 0<n) : |A-A'|≤W+D/(n:ℝ) := by
    have nr : 0<(n:ℝ) := by exact_mod_cast np
    let S:=b*sumaDeNumerador n p r c/(n:ℝ)^2
    let S':=v*sumaDeNumerador n q r c/(n:ℝ)^2
    have middle : |S-S'|≤W := by
      dsimp only [S,S']; rw [←sub_div,abs_div,abs_of_pos (pow_pos nr 2)]
      apply (div_le_iff₀ (pow_pos nr 2)).mpr
      unfold sumaDeNumerador
      rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,mul_comm W]
      exact acotar_la_suma _ W (fun e => cambio_con_coeficiente sp sq kp bp close hr hc
        (medio_admisible e.1.isLt) (medio_admisible e.2.isLt))
    have left:=error_integral_del_cruce sp kp lp bp n np hr hc
    have right:=error_integral_del_cruce sq kp lp vp n np hr hc
    have tri:= (abs_sub_le A S A').trans (add_le_add_left (abs_sub_le S S' A') _)
    rw [abs_sub_comm S' A'] at tri
    apply tri.trans
    apply (add_le_add left (add_le_add middle right)).trans_eq
    dsimp [D,W]; ring
  apply le_of_tendsto_of_tendsto (f:=fun _ : ℕ => |A-A'|) (g:=fun n : ℕ => W+D/(n:ℝ))
    tendsto_const_nhds (by
      simpa using (tendsto_const_nhds (x:=W)).add (tendsto_const_div_atTop_nhds_zero_nat D)) ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n np
  exact est n np

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparar_dos_perfiles
