import ParametrosDeLasColasEnLaReservaDelArticulo
import ErrorDeEntropiaEnLaEscalaDeReserva
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter
open scoped Topology

def errorFisicoReserva (κ ν : ℝ) (n : ℕ) : ℝ :=
  let η:=κ*fraccionReserva n/4
  (430*(ν/η^4)*log n/sqrt (n-huecosReserva n : ℕ))*(1/η)^12

theorem error_fisico_incluso_en_dos_fracciones {κ ν : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    Tendsto (fun n=>errorFisicoReserva κ ν n/(fraccionReserva n)^2) atTop (𝓝 0) := by
  let C:=860*ν*(4/κ)^16
  have cp : 0≤C:=by dsimp [C]; positivity
  have dom : Tendsto (fun n=>C*errorDeLaReserva n) atTop (𝓝 0):=by
    simpa using error_de_reserva_tiende_a_cero.const_mul C
  have logs:=((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine squeeze_zero_norm' ?_ dom
  filter_upwards [cortes_de_la_reserva,fraccion_de_reserva_tiende_a_cero.eventually_lt_const
    (by norm_num : (0:ℝ)<1/2),eventually_ge_atTop 1,logs] with n cut small hn lg
  let x:=fraccionReserva n
  let q:=n-huecosReserva n
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have xp : 0<x:=div_pos (by exact_mod_cast cut.1) np
  have eq : x*n=(huecosReserva n:ℝ):=by dsimp [x,fraccionReserva]; field_simp
  have qeq : (q:ℝ)=(n:ℝ)-(huecosReserva n:ℝ):=Nat.cast_sub cut.2.1
  have half : (n:ℝ)/2≤q:=by
    have e:=mul_le_mul_of_nonneg_right (show x≤1/2 from small.le) np.le
    linarith only [eq,e,qeq]
  have qp : 0<(q:ℝ):=by linarith
  have sq:=Real.sqrt_pos.mpr qp
  have sn:=Real.sqrt_pos.mpr np
  have cmp : sqrt (n:ℝ)≤2*sqrt (q:ℝ):=by
    nlinarith only [Real.sq_sqrt np.le,Real.sq_sqrt qp.le,half,sn,sq]
  change 1≤log (n:ℝ) at lg
  have l0 : 0≤log n:=by linarith only [lg]
  have l2 : log n≤(log n)^2:=by nlinarith only [mul_nonneg l0 (sub_nonneg.mpr lg)]
  have ratio : log n/sqrt q≤2*((log n)^2/sqrt n):=by
    apply (div_le_iff₀ sq).mpr
    rw [mul_div_assoc',div_mul_eq_mul_div]
    apply (le_div_iff₀ sn).mpr
    have z:=mul_le_mul_of_nonneg_left cmp l0
    have w:=mul_le_mul_of_nonneg_right l2 sq.le
    nlinarith only [z,w]
  let M:=430*ν*(4/κ)^16*(1/x)^18
  have mn : 0≤M:=by dsimp [M]; positivity
  have form : errorFisicoReserva κ ν n/x^2=M*(log n/sqrt q):=by
    dsimp only [errorFisicoReserva,M]
    change (430*(ν/(κ*x/4)^4)*log n/sqrt q)*(1/(κ*x/4))^12/x^2=_
    field_simp [kp.ne',xp.ne',sq.ne']; ring
  have lnx : 0≤log (1/x):=Real.log_nonneg ((one_le_div xp).mpr (by linarith only [small] : x≤1))
  have second : 0≤(n:ℝ)^(-exponenteReserva)*log (1/x):=by positivity
  change ‖errorFisicoReserva κ ν n/x^2‖≤_
  rw [form,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg mn (div_nonneg l0 sq.le))]
  calc
    M*(log n/sqrt q) ≤ M*(2*((log n)^2/sqrt n)):=mul_le_mul_of_nonneg_left ratio mn
    _ = C*((1/x)^18*(log n)^2/sqrt n):=by dsimp [M,C]; ring
    _ ≤ C*errorDeLaReserva n:=mul_le_mul_of_nonneg_left (by unfold errorDeLaReserva; linarith only [second]) cp
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_fisico_incluso_en_dos_fracciones
