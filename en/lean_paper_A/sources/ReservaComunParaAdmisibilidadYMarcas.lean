import ControlSimultaneoDeLaMasaDeReserva
import UnaMismaReservaEnB1YEnElProcesoG
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
open Real
/-- Allows the candidate mass to be combined with any other event of the same reserve. -/
theorem existe_reserva_comun {ι : Type} [Fintype ι] (τ : ℝ) (prob : τ∈Set.Icc (0:ℝ) 1)
    (P E : (ι→Bool)→Prop)
    (union : mediaCubo τ (fun ω=>if ¬P ω then 1 else 0)+mediaCubo τ (fun ω=>if E ω then 1 else 0)<1) :
    ∃ ω,P ω ∧ ¬E ω := by
  by_contra! h
  let a (ω : ι→Bool) : ℝ:=if ¬P ω then 1 else 0
  let b (ω : ι→Bool) : ℝ:=if E ω then 1 else 0
  have both (ω) : 1≤a ω+b ω:=by by_cases hp : P ω <;> simp [a,b,hp,h ω]; split <;> norm_num
  have lower:=mediaCubo_mono prob (f:=fun _=>1) (g:=fun ω=>a ω+b ω) both
  rw [mediaCubo_const] at lower
  have add : mediaCubo τ (fun ω=>a ω+b ω)=mediaCubo τ a+mediaCubo τ b:=by
    simp [mediaCubo,mul_add,Finset.sum_add_distrib]
  exact (not_lt_of_ge (lower.trans_eq add)) union

set_option maxHeartbeats 1200000 in
theorem reserva_con_masa_para_el_proceso_G {n : ℕ} (posn : 1≤n) (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (rows : ∀ i,masaBajo w (fun e=>e.1=i)≤1) (cols : ∀ i,masaBajo w (fun e=>e.2=i)≤1)
    (diag : ∀ i,masaBajo w (fun e=>i∈lineasPropias e)≤1) (τ q : ℝ)
    (pτ : 0≤τ) (pe : τ≤1/8) (mass : (∑ e : Cell n,w e)=q)
    (qmin : 4≤q) (qmax : q≤n) (half : (n:ℝ)/2≤q) (P : (LineaReservable n→Bool)→Prop)
    (good : mediaCubo τ (fun ω=>if ¬P ω then 1 else 0)+(n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296)<1) :
    ∃ ω,P ω ∧ ∀ (factor : ℝ),1≤factor → ∀ z, τ^4*q/8 ≤ masaBajo
      (fun e=>if quedaTrasReserva ω e then factor*w e else 0)
      (marcasDeG (oblicuaMarcada ω etiquetaD 2) (oblicuaMarcada ω etiquetaA 3) z) := by
  have hp : τ∈Set.Icc (0:ℝ) 1:=⟨pτ,by linarith only [pe]⟩
  have bad:=cola_para_todas_las_raices_de_B1 (n:=n) posn w pos rows cols diag τ q pτ pe mass qmin qmax half
  let E (u : LineaReservable n→Bool) : Prop := ∃ z,masaMarcadaB1 w z u≤τ^4*q/8
  let t : ℝ := mediaCubo τ (fun ω=>if ¬P ω then 1 else 0)
  have hb : mediaCubo τ (fun u=>if E u then 1 else 0) ≤ (n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296) := by
    unfold E
    exact bad
  have bound : t + mediaCubo τ (fun u=>if E u then 1 else 0)<1 := by
    calc
      _ ≤ t + (n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296) := add_le_add le_rfl hb
      _ < 1 := good
  have someReserve : ∃ ω : LineaReservable n→Bool, P ω ∧ ¬E ω := by
    apply existe_reserva_comun τ hp P E
    have flags : (fun u => @ite ℝ (E u) (Classical.propDecidable _) 1 0) =
        (fun u => if E u then (1:ℝ) else 0) := by
      funext u
      by_cases hu : E u <;> simp only [hu,if_pos,if_neg]
    rw [flags]
    exact bound
  obtain ⟨ω,hω,no⟩:=someReserve
  refine ⟨ω,hω,fun factor he z=>?_⟩
  have raw : τ^4*q/8≤masaMarcadaB1 w z ω:=le_of_lt (lt_of_not_ge (fun low=>no ⟨z,low⟩))
  exact raw.trans (masa_tras_normalizar_la_reserva (n:=n) w pos factor he ω z)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existe_reserva_comun
#print axioms ArticuloA.Historias.reserva_con_masa_para_el_proceso_G
