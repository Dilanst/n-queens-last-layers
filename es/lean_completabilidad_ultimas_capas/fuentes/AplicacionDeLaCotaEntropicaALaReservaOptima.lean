import EntropiaDelCaminoConErrorExplicito
import MarcaLogaritmicaEnLaReservaDelArticulo
import PerdidasSublinealesDeLaEntropiaDeG
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Filter
open scoped Topology
theorem el_error_sobre_la_holgura_se_anula {κ ν : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    Tendsto (fun n=>errorFisicoReserva κ ν n/(κ*fraccionReserva n/4)) atTop (𝓝 0) := by
  have h:=((error_fisico_incluso_en_dos_fracciones kp vn).mul fraccion_de_reserva_tiende_a_cero).const_mul (4/κ)
  simp only [mul_zero,zero_mul] at h
  apply h.congr'
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1] with n cut hn
  have xp : 0<fraccionReserva n:=div_pos (by exact_mod_cast cut.1) (by exact_mod_cast (show 0<n by omega))
  field_simp [xp.ne',kp.ne']; ring

theorem entropia_fisica_de_cualquier_peso_en_la_reserva {κ ν : ℝ} (kp : 0<κ) (v1 : 1≤ν) :
    ∀ᶠ n : ℕ in atTop,let q:=n-huecosReserva n
      let η:=κ*fraccionReserva n/4
      ∀ v : Cell n→ℝ≥0,(∑ e,(v e:ℝ))=q→(∀ e,(v e:ℝ)≤ν/n)→(∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)→
      entropiaDiscretaDeReserva (fun e=>(v e:ℝ))-(2+log n+(n:ℝ)*gastoPorEleccion κ ν n)≤
        entropiaDeEstados (rutas (pasoDeG v q) 0 q (some []))-log q.factorial := by
  have vn : 0≤ν:=by linarith
  have tiny:=(error_fisico_tiende_a_cero kp vn).eventually_lt_const (by norm_num : (0:ℝ)<1/10)
  have close:=(el_error_sobre_la_holgura_se_anula kp vn).eventually_lt_const (by norm_num : (0:ℝ)<1/8)
  have logs:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ)
  have nb:=(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop ν
  filter_upwards [parametros_del_seguimiento_en_la_reserva kp,tiny,close,logs,nb,
    cola_del_logaritmo_en_la_escala_de_la_reserva,eventually_ge_atTop 2] with n pars tol rel log1 big tail n2
  intro q η v mass cap slack
  obtain ⟨np,qp,hp,h4,sm,l0,scale⟩:=pars
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have qn : q≤n:=Nat.sub_le _ _
  have logq:=Real.log_le_log qr (show (q:ℝ)≤n by exact_mod_cast qn)
  have cap1 e : (v e:ℝ)≤1:=(cap e).trans ((div_le_one nr).mpr big)
  obtain ⟨sz,repr⟩:=la_marca_del_logaritmo_esta_normalizada v (by exact_mod_cast (show 1<n by omega)) cap1
  let E:=errorFisicoReserva κ ν n
  have en : 0≤E:=by
    change 0≤(430*(ν/η^4)*log n/sqrt (q:ℝ))*(1/η)^12
    positivity
  have h1 : η≤1:=h4.trans (by norm_num)
  have tail' t (ht : t<q) :=
    (cola_del_prefijo_con_una_marca_real np qp qn v mass (pruebasDeEntropia v) false true t ht.le (fun _=>rfl)
      (fun i e=>(sz i e).1) (fun i e=>(sz i e).2) hp h4 v1 log1 scale cap slack sm tol.le).trans tail
  have sm' : 1/(η*q)≤1/2:=by
    have b:=div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤5/4) (mul_nonneg hp.le qr.le)
    exact (b.trans sm).trans (by norm_num)
  have finite:=entropia_de_la_trayectoria_con_error_finito np qp v (pruebasDeEntropia v) true hp h1 en tol.le
    (by positivity : 0≤2*log n) mass (sz true) repr sm' slack tail'
  let H:=E/((9/10)*η*q)
  let b:=exp (2*H*q)
  let vCost:=2*E+4*log n*(E+8*E/η)+(25/(n:ℝ)^2)*(2*log n)
  have er:=costo_de_lineas_de_orden_dos qr hp en rel.le
  change 4*q*((b-1)+b*H*q)/η≤(q:ℝ)*(32*(E/η^2)) at er
  have non : 0≤vCost+32*(E/η^2):=by dsimp [vCost]; positivity
  have qq:=mul_le_mul_of_nonneg_right (show (q:ℝ)≤n by exact_mod_cast qn) non
  change entropiaDiscretaDeReserva _-(2+log q+q*(2*E+2*(2*log n)*(E+8*E/η)+25/(n:ℝ)^2*(2*log n))+
    4*q*((b-1)+b*H*q)/η)≤_ at finite
  apply le_trans _ finite
  change _-(2+log n+n*(vCost+32*(E/η^2)))≤_
  rw [mul_add] at qq
  have ev : 2*E+2*(2*log n)*(E+8*E/η)+25/(n:ℝ)^2*(2*log n)=vCost:=by dsimp [vCost]; ring
  rw [ev]
  linarith only [er,qq,logq]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_fisica_de_cualquier_peso_en_la_reserva
