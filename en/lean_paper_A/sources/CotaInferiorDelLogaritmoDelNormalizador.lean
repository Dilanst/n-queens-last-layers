import FibrasDeLaCuadraturaEnLaReserva
import MasasDelOptimoEnLosIntervalos
namespace ArticuloA.Historias
open Perfil Real
open scoped NNReal BigOperators
noncomputable section

/-- To bound the entropy from below, what matters is the direction opposite to the one used in the KL of E2. -/
theorem normalizador_logaritmico_desde_abajo {n q : ℕ} {p : FactoresContinuos} {κ M L b x : ℝ}
    (hn : 0<n) (hq : 0<q) (qn : q≤n) (kp : 0<κ) (mp : 0≤M) (lp : 0≤L)
    (bp : 0<b) (xp : 0<x) (sp : ControlEspacial p κ M L)
    (mass : integralTablero (pesoContinuo p)=((q:ℝ)/n)/b) :
    (q:ℝ)*(log n+log q-log (b/x^2)-log (x^2*Wfisico n p))≤2*(4*M^3*L)/κ^4 := by
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have qp : 0<(q:ℝ):=by exact_mod_cast hq
  have low:=masa_inferior (n:=n) sp kp.le
  have wp : 0<Wfisico n p:=(mul_pos (pow_pos kp _) (pow_pos np 2)).trans_le low
  let U:=(n:ℝ)^2*integralTablero (pesoContinuo p)
  have ref : U=(n:ℝ)*q/b := by dsimp [U]; rw [mass]; field_simp; ring
  have up : 0<U:=by rw [ref]; exact div_pos (mul_pos np qp) bp
  have lg:=log_sobre_referencia U (Wfisico n p) up wp
  have ub : Wfisico n p*(log U-log (Wfisico n p))≤2*(4*M^3*L)*n :=
    lg.trans (by dsimp [U]; linarith only [(abs_le.mp (cuadratura_total_fisica hn sp mp lp)).1])
  have scale : (q:ℝ)*(2*(4*M^3*L)*n)*κ^4≤2*(4*M^3*L)*Wfisico n p := by
    have cpos : 0≤2*(4*M^3*L):=by positivity
    have qb : (q:ℝ)≤n:=by exact_mod_cast qn
    have ref2:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right qb np.le) (mul_nonneg cpos (pow_nonneg kp.le 4))
    nlinarith only [ref2,mul_le_mul_of_nonneg_left low cpos]
  have den : log U-log (Wfisico n p)≤(2*(4*M^3*L)*n)/Wfisico n p:=
    (le_div_iff₀ wp).mpr (by simpa [mul_comm] using ub)
  have final := mul_le_mul_of_nonneg_left den qp.le
  have scaled : (q:ℝ)*((2*(4*M^3*L)*n)/Wfisico n p)≤2*(4*M^3*L)/κ^4 := by
    rw [←mul_div_assoc,div_le_div_iff₀ wp (pow_pos kp 4)]
    exact scale
  have logs : log n+log q-log (b/x^2)-log (x^2*Wfisico n p)=log U-log (Wfisico n p) := by
    rw [ref,log_div bp.ne' (pow_ne_zero 2 xp.ne'),log_mul (pow_ne_zero 2 xp.ne') wp.ne',
      log_div (mul_ne_zero np.ne' qp.ne') bp.ne',log_mul np.ne' qp.ne']
    ring
  rw [logs]
  exact final.trans scaled
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizador_logaritmico_desde_abajo
