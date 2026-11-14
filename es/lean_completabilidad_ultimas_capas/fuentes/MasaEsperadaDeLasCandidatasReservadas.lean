import EtiquetasDeLasOblicuasDeLaReserva
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
def masaMarcadaB1 {n} (w : Cell n→ℝ) (z : Cell n) (ω : LineaReservable n→Bool) : ℝ :=
  ∑ e : Cell n,if acuerdoDeReserva (lineasSolicitadas z e) (lineasPropias e) ω then w e else 0

theorem media_marcada_como_suma_de_cilindros {n} (w : Cell n→ℝ) (z : Cell n) (τ : ℝ) :
    (∑ ω : LineaReservable n→Bool, masaDeReserva τ ω*masaMarcadaB1 w z ω)=
      ∑ e : Cell n,w e*∑ ω : LineaReservable n→Bool,
        (if acuerdoDeReserva (lineasSolicitadas z e) (lineasPropias e) ω then masaDeReserva τ ω else 0) := by
  unfold masaMarcadaB1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : acuerdoDeReserva (lineasSolicitadas z e) (lineasPropias e) ω <;> simp [h,mul_comm]

theorem masa_fuera_de_los_ejes {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e) (z : Cell n)
    (hr : (∑ e : Cell n,if z.1=e.1 then w e else 0)≤1)
    (hc : (∑ e : Cell n,if z.2=e.2 then w e else 0)≤1) :
    (∑ e : Cell n,w e)-2≤∑ e : Cell n,if z.1≠e.1 ∧ z.2≠e.2 then w e else 0 := by
  have pointw (e : Cell n) : w e≤(if z.1=e.1 then w e else 0)+(if z.2=e.2 then w e else 0)+
      (if z.1≠e.1 ∧ z.2≠e.2 then w e else 0):=by
    by_cases a : z.1=e.1 <;> by_cases b : z.2=e.2 <;> simp [a,b,pos]
  have all:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>pointw e)
  simp only [Finset.sum_add_distrib] at all
  linarith only [all,hr,hc]

theorem cota_media_marcada_de_B1 {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e) (z : Cell n)
    (hr : (∑ e : Cell n,if z.1=e.1 then w e else 0)≤1)
    (hc : (∑ e : Cell n,if z.2=e.2 then w e else 0)≤1) (τ : ℝ) (prob : τ∈Set.Icc (0:ℝ) 1) :
    τ^4*(1-τ)^2*((∑ e : Cell n,w e)-2)≤∑ ω : LineaReservable n→Bool, masaDeReserva τ ω*masaMarcadaB1 w z ω := by
  rw [media_marcada_como_suma_de_cilindros]
  have c:=mul_le_mul_of_nonneg_left (masa_fuera_de_los_ejes w pos z hr hc) (mul_nonneg (by positivity : 0≤τ^4) (sq_nonneg (1-τ)))
  apply c.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  by_cases axes : z.1≠e.1 ∧ z.2≠e.2
  · rw [if_pos axes,mul_comm _ (w e)]
    exact mul_le_mul_of_nonneg_left (esperanza_de_marca_individual τ prob z e axes.1 axes.2) (pos e)
  · rw [if_neg axes,mul_zero]
    apply mul_nonneg (pos e)
    apply Finset.sum_nonneg
    intro ω _
    split
    · exact masa_de_reserva_no_negativa τ prob ω
    · exact le_rfl

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_marcada_como_suma_de_cilindros
#print axioms ArticuloA.Historias.masa_fuera_de_los_ejes
#print axioms ArticuloA.Historias.cota_media_marcada_de_B1
