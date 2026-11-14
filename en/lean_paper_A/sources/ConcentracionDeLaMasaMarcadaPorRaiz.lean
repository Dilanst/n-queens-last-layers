import TresLineasControlanUnaReservaMarcada
import ColaParaUnSorteoDeOblicuas
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
open Real

set_option maxHeartbeats 1200000 in
theorem raiz_con_poca_masa_tiene_cola {n : ℕ} (posn : 1≤n) (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (rows : ∀ i,masaBajo w (fun e=>e.1=i)≤1) (cols : ∀ i,masaBajo w (fun e=>e.2=i)≤1)
    (diag : ∀ j,masaBajo w (fun e=>j∈lineasPropias e)≤1) (z : Cell n)
    (τ q : ℝ) (pτ : 0≤τ) (pe : τ≤1/8) (mass : (∑ e : Cell n,w e)=q)
    (qmin : 4≤q) (qmax : q≤n) (half : (n:ℝ)/2≤q) :
    mediaCubo τ (fun ω=>if masaMarcadaB1 w z ω≤τ^4*q/8 then 1 else 0) ≤
      exp (-(τ^8)*(n:ℝ)/55296) := by
  let f:=masaMarcadaB1 w z
  let m : ℝ:=Fintype.card (LineaReservable n)
  let t:=τ^4*q/8
  let θ:=t/(18*m)
  have mval : m=4*(n:ℝ)+2:=by simp [m,LineaReservable]; ring
  have nn : (1:ℝ)≤n:=by exact_mod_cast posn
  have mp : 0<m:=by linarith only [mval,nn]
  have mt : m≤6*(n:ℝ):=by linarith only [mval,nn]
  have qp : 0≤q:=by linarith only [qmin]
  have ltau : τ≤1:=by linarith only [pe]
  have pow1 : τ^4≤1:=pow_le_one₀ pτ ltau
  have tp : 0≤t:=by dsimp [t]; positivity
  have ts : t≤n/8:=by dsimp [t]; linarith only [mul_le_mul_of_nonneg_right pow1 qp,qmax]
  have pθ : 0≤θ:=div_nonneg tp (by positivity)
  have small : θ*3≤1:=by
    calc
      _ = (t*3)/(18*m) := by dsimp [θ]; ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [ts,mval,nn])
  have hr : (∑ e : Cell n,if z.1=e.1 then w e else 0)≤1:=by
    simpa [masaBajo,pesoCuando,eq_comm] using rows z.1
  have hc : (∑ e : Cell n,if z.2=e.2 then w e else 0)≤1:=by
    simpa [masaBajo,pesoCuando,eq_comm] using cols z.2
  have mean := cota_media_en_la_escala_de_B1 w pos z hr hc τ pτ pe (by rw [mass]; exact qmin)
  rw [mass] at mean
  have toCubo : (∑ ω : LineaReservable n→Bool,masaDeReserva τ ω*masaMarcadaB1 w z ω)=mediaCubo τ f:=by
    unfold mediaCubo
    apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl
  rw [toCubo] at mean
  have pointw (u : LineaReservable n→Bool) :
      (if f u≤t then (1:ℝ) else 0)≤(if f u≤mediaCubo τ f-t then 1 else 0):=by
    by_cases a : f u≤t
    · have b : f u≤mediaCubo τ f-t:=by dsimp [t] at a ⊢; linarith only [a,mean]
      simp [a,b]
    · simp [a]; split <;> norm_num
  apply (mediaCubo_mono ⟨pτ,ltau⟩ pointw).trans
  have mg:=cola_inferior_para_limite_tres (t:=t) ⟨pτ,ltau⟩ pθ small f
    (fun j ω ω' h=>cambiar_una_reserva_cuesta_a_lo_sumo_tres w pos rows cols diag z ω ω' j h)
  apply mg.trans
  apply Real.exp_le_exp.mpr
  change m*(θ*3)^2-θ*t≤_
  have optim : m*(θ*3)^2-θ*t= -t^2/(36*m):=by dsimp [θ]; field_simp; ring
  rw [optim]
  apply (div_le_iff₀ (by positivity : 0<36*m)).mpr
  have q2:=sq_le_sq' (show -(q)≤(n:ℝ)/2 by linarith only [nn,qp]) half
  have mass2:=mul_le_mul_of_nonneg_left mt (show 0≤(τ^8)*(n:ℝ) by positivity)
  have qp2:=mul_le_mul_of_nonneg_left q2 (show 0≤τ^8 by positivity)
  dsimp [t]
  nlinarith only [mass2,qp2]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.raiz_con_poca_masa_tiene_cola
