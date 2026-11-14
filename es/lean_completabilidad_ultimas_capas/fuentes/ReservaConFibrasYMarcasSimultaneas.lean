import EscalaDeLaConcentracionDeFibras
import ReservaComunParaAdmisibilidadYMarcas
import NormalizacionFisicaDeLaReserva
import NumeroDeOblicuasReservadas
namespace ArticuloA.Historias
open Repair Limites Real Filter
noncomputable section
open Classical
open scoped BigOperators Topology

theorem reserva_con_fibras_y_marcas_en_la_escala_original (A : ℝ) (ap : 0<A) :
    ∀ᶠ n : ℕ in atTop, ∀ (w : Cell n→ℝ) (q : ℝ), (∀ e,0≤w e) → (∀ e,w e≤A/n) →
      (∀ i,masaBajo w (fun e=>e.1=i)≤1) → (∀ i,masaBajo w (fun e=>e.2=i)≤1) →
      (∀ j,masaBajo w (fun e=>j∈lineasPropias e)≤1) →
      (∑ e : Cell n,w e)=q → 4≤q → q≤n → (n:ℝ)/2≤q →
      let τ:=(n:ℝ)^(-exponenteReserva)
      let t:=(n:ℝ)^(-(1/4:ℝ))
      ∃ u : LineaReservable n→Bool, (∀ i : FibraDeB1 n,|masaAuxiliar w i u-centroDeLaFibra τ w i|≤t) ∧
        numeroDeReservas u≤2*(Fintype.card (LineaReservable n):ℝ)*τ ∧ ∀ factor : ℝ,1≤factor → ∀ z : Cell n,τ^4*q/8≤masaBajo
          (fun e=>if quedaTrasReserva u e then factor*w e else 0)
          (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z) := by
  have small : Tendsto (fun n : ℕ=>(n:ℝ)^(-exponenteReserva)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num [exponenteReserva])).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,small.eventually_lt_const (by norm_num : (0:ℝ)<1/8),
    fibras_con_peso_sobre_n_tienen_fallo_a_lo_sumo_n_menos_cuatro A ap,
    cola_de_la_reserva_es_eventualmente_inferior_a_n_menos_cuatro] with n n2 pe rare tail
  intro w q pos cap rows cols diag mass qm qM half
  let τ:=(n:ℝ)^(-exponenteReserva)
  let t:=(n:ℝ)^(-(1/4:ℝ))
  have hp : τ∈Set.Icc (0:ℝ) 1 := ⟨by dsimp [τ]; positivity,pe.le.trans (by norm_num)⟩
  let regular (u : LineaReservable n→Bool) : Prop := ∀ i : FibraDeB1 n,|masaAuxiliar w i u-centroDeLaFibra τ w i|≤t
  have incl (u : LineaReservable n→Bool) : (if ¬regular u then (1:ℝ) else 0)≤
      (if ∃ i : FibraDeB1 n,t≤|masaAuxiliar w i u-centroDeLaFibra τ w i| then 1 else 0) := by
    by_cases h : regular u
    · rw [if_neg (not_not.mpr h)]
      split <;> norm_num
    · rw [if_pos h]
      have h' : ¬∀ i : FibraDeB1 n,|masaAuxiliar w i u-centroDeLaFibra τ w i|≤t := h
      push_neg at h'
      obtain ⟨i,hi⟩:=h'
      rw [if_pos (show ∃ i : FibraDeB1 n,t≤|masaAuxiliar w i u-centroDeLaFibra τ w i| from ⟨i,hi.le⟩)]
  have bad:=(mediaCubo_mono hp incl).trans (rare w τ hp (fun e=>by rw [abs_of_nonneg (pos e)]; exact cap e))
  have nr : (2:ℝ)≤n:=by exact_mod_cast n2
  let m : ℝ := Fintype.card (LineaReservable n)
  have mp : 0<m := by
    simp [m,LineaReservable,Fintype.card_prod]; positivity
  have τp : 0<τ := Real.rpow_pos_of_pos (by positivity) _
  let short (u : LineaReservable n→Bool) := numeroDeReservas u≤2*m*τ
  let P (u : LineaReservable n→Bool) := regular u ∧ short u
  let b (u : LineaReservable n→Bool) : ℝ := if ¬regular u then 1 else 0
  let c (u : LineaReservable n→Bool) : ℝ := if 2*m*τ<numeroDeReservas u then 1 else 0
  have prodBad (u) : (if ¬P u then (1:ℝ) else 0)≤b u+c u := by
    by_cases g : regular u <;> by_cases k : 2*m*τ<numeroDeReservas u
    · simp [P,short,b,c,g,k,not_le.mpr k]
    · simp [P,short,b,c,g,k,le_of_not_gt k]
    · simp [P,short,b,c,g,k]
    · simp [P,short,b,c,g,k]
  have add : mediaCubo τ (fun u=>b u+c u)=mediaCubo τ b+mediaCubo τ c := by
    simp [mediaCubo,mul_add,Finset.sum_add_distrib]
  have probBad:=(mediaCubo_mono hp prodBad).trans_eq add
  have ct : mediaCubo τ c≤1/2 := cola_del_numero_de_reservas hp (mul_pos mp τp)
  have rest : 1/(n:ℝ)^4+1/(n:ℝ)^4<1/2 := by
    have four : (2:ℝ)^4≤(n:ℝ)^4:=by gcongr
    rw [←add_div]
    apply (div_lt_iff₀ (by positivity : 0<(n:ℝ)^4)).mpr
    linarith only [four]
  have together : mediaCubo τ (fun u=>if ¬P u then 1 else 0)+(n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296)<1 := by
    have rb : mediaCubo τ b≤1/(n:ℝ)^4 := bad
    change (n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296)≤1/(n:ℝ)^4 at tail
    linarith only [probBad,rb,ct,tail,rest]
  have existsGood : ∃ u : LineaReservable n→Bool,P u ∧ ∀ factor : ℝ,1≤factor → ∀ z : Cell n,
      τ^4*q/8≤masaBajo (fun e=>if quedaTrasReserva u e then factor*w e else 0)
        (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z) := by
    apply reserva_con_masa_para_el_proceso_G (n:=n) (by omega) w pos rows cols diag τ q hp.1 pe.le mass qm qM half P
    apply lt_of_le_of_lt _ together
    apply add_le_add_right
    apply mediaCubo_mono hp
    intro u
    by_cases ok : P u <;> simp [ok]
  obtain ⟨u,hP,marks⟩:=existsGood
  exact ⟨u,hP.1,hP.2,marks⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reserva_con_fibras_y_marcas_en_la_escala_original
