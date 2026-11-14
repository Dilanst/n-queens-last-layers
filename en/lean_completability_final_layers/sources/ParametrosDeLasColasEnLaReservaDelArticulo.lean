import BalanceUniformeParaElNumeroDeHuecosVariable
import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open Filter Real
open scoped Topology
noncomputable section

theorem parametros_del_seguimiento_en_la_reserva {κ : ℝ} (kp : 0<κ) :
    ∀ᶠ n : ℕ in atTop,let q:=n-huecosReserva n
      let η:=κ*fraccionReserva n/4
      0<n ∧ 0<q ∧ 0<η ∧ η≤1/4 ∧ (5/4)/(η*q)≤1/16 ∧ 0≤log n ∧ log n≤sqrt (q:ℝ) := by
  have small : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^(1/2:ℝ)) atTop (𝓝 0):=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,cortes_de_la_reserva,
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const (one_div_pos.mpr kp),
    la_reserva_supera_cualquier_umbral_de_huecos (160/κ),small.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with n hn cuts half tight big logs
  intro q η
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have x : 0<fraccionReserva n:=div_pos (by exact_mod_cast (show 0<huecosReserva n from cuts.1)) np
  have mulx : fraccionReserva n*n=(huecosReserva n:ℝ):=by dsimp [fraccionReserva]; field_simp
  have hq : (q:ℝ)=(n:ℝ)-(huecosReserva n:ℝ):=Nat.cast_sub cuts.2.1
  have qhalf : (n:ℝ)/2≤q:=by have h:=mul_le_mul_of_nonneg_right half.le np.le; linarith only [mulx,h,hq]
  have qr : 0<(q:ℝ):=by linarith only [qhalf,np]
  have hp : 0<η:=by dsimp [η]; positivity
  have etamax : η≤1/4:=by
    have b:=(lt_div_iff₀ kp).mp tight
    dsimp [η]; nlinarith only [b]
  have eq : η*n=(κ*(huecosReserva n:ℝ))/4:=by dsimp [η]; rw [←mulx]; ring
  have thresh : (20:ℝ)≤η*q:=by
    have a:=(div_le_iff₀ kp).mp big
    have b:=mul_le_mul_of_nonneg_left qhalf hp.le
    nlinarith only [a,b,eq]
  have lg : 0≤log n:=Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  refine ⟨by omega,by exact_mod_cast qr,hp,etamax,(div_le_iff₀ (mul_pos hp qr)).mpr (by linarith),lg,?_⟩
  rw [←Real.sqrt_eq_rpow] at logs
  have y:=(div_lt_iff₀ (Real.sqrt_pos.mpr np)).mp logs
  have z : (sqrt (n:ℝ)/2)^2≤q:=by nlinarith only [Real.sq_sqrt np.le,qhalf,np]
  have upper:=Real.sq_sqrt qr.le
  have s:=Real.sqrt_nonneg (q:ℝ)
  nlinarith only [z,upper,s,y,lg]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.parametros_del_seguimiento_en_la_reserva
