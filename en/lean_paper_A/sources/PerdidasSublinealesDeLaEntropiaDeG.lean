import PrimeraSalidaConLaReservaDelOptimoFisico
import EscalaDeLaProbabilidadDeFalloFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Filter
open scoped Topology
def gastoPorEleccion (κ ν : ℝ) (n : ℕ) : ℝ :=
  let η:=κ*fraccionReserva n/4
  let E:=errorFisicoReserva κ ν n
  2*E+4*log n*(E+8*E/η)+(25/(n:ℝ)^2)*(2*log n)+32*(E/η^2)

theorem costo_de_lineas_de_orden_dos {q η E : ℝ} (qp : 0<q) (hp : 0<η) (en : 0≤E)
    (close : E/η≤1/8) :
    let H:=E/((9/10)*η*q)
    let b:=exp (2*H*q)
    4*q*((b-1)+b*H*q)/η≤q*(32*(E/η^2)) := by
  intro H b
  let z:=H*q
  have eq : z=(10/9)*(E/η):=by dsimp [z,H]; field_simp; ring
  have zn : 0≤z:=by rw [eq]; positivity
  have small : 2*z≤1/2:=by linarith only [eq,close]
  have ep:=Real.exp_bound_div_one_sub_of_interval (by positivity : 0≤2*z) (by linarith : 2*z<1)
  have pp : 0<1-2*z:=by linarith
  have bb : b≤1+4*z:=by
    change exp (2*H*q)≤_
    rw [show 2*H*q=2*z by dsimp [z]; ring]
    apply ep.trans
    apply (div_le_iff₀ pp).mpr
    nlinarith only [mul_nonneg zn (show 0≤1-4*z by linarith)]
  have b2 : b≤2:=by linarith only [bb,small]
  have bz:=mul_le_mul_of_nonneg_right b2 zn
  have bd : (b-1)+b*H*q≤6*z:=by rw [mul_assoc b H q]; change (b-1)+b*z≤6*z; linarith only [bz,bb]
  have last:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left bd (by positivity : 0≤4*q)) hp.le
  apply last.trans
  rw [eq]
  have ae : 4*q*(6*((10/9)*(E/η)))/η=(80/3)*q*(E/η^2):=by ring
  rw [ae]
  nlinarith only [mul_nonneg qp.le (div_nonneg en (sq_nonneg η))]

theorem costo_medio_de_la_reserva_tiende_a_cero {κ ν : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    Tendsto (gastoPorEleccion κ ν) atTop (𝓝 0) := by
  let x:=fraccionReserva
  let η n:=κ*x n/4
  let E:=errorFisicoReserva κ ν
  have e0:=error_fisico_tiende_a_cero kp vn
  have r0:=error_fisico_incluso_en_dos_fracciones kp vn
  have η0 : Tendsto η atTop (𝓝 0):=by simpa [η,x] using (fraccion_de_reserva_tiende_a_cero.const_mul κ).div_const 4
  have ratio : Tendsto (fun n=>E n/(η n)^2) atTop (𝓝 0):=by
    have h:=r0.const_mul ((4/κ)^2)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards with n
    dsimp [η,x,E]
    ring
  have xl : Tendsto (fun n=>x n*log n) atTop (𝓝 0):=by
    have h:=perdida_de_marcas_en_la_escala_de_G.div_const 4
    simp only [zero_div] at h
    apply h.congr'
    filter_upwards with n
    dsimp [x,fraccionReserva]; ring
  have yl : Tendsto (fun n=>η n*log n) atTop (𝓝 0):=by
    have h:=xl.const_mul (κ/4)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards with n
    dsimp [η]; ring
  have lg : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)) atTop (𝓝 0):=by
    simpa using ((isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have inv:=tendsto_const_div_atTop_nhds_zero_nat 1
  have combined:=(((e0.const_mul 2).add ((((ratio.mul yl).mul η0).add ((ratio.mul yl).const_mul 8)).const_mul 4)).add
    ((lg.mul inv).const_mul 50)).add (ratio.const_mul 32)
  simp only [zero_mul,mul_zero,add_zero] at combined
  apply combined.congr'
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1] with n cut nn
  have np : 0<(n:ℝ):=by exact_mod_cast nn
  have xp : 0<x n:=div_pos (by exact_mod_cast cut.1) np
  have hp : 0<η n:=by dsimp [η]; positivity
  change 2*E n+4*((E n/(η n)^2*(η n*log n))*η n+8*(E n/(η n)^2*(η n*log n)))+
      50*(log n/(n:ℝ)*(1/(n:ℝ)))+32*(E n/(η n)^2)=_
  change _=2*E n+4*log n*(E n+8*E n/η n)+(25/(n:ℝ)^2)*(2*log n)+32*(E n/(η n)^2)
  field_simp [hp.ne',np.ne']; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.costo_medio_de_la_reserva_tiende_a_cero
