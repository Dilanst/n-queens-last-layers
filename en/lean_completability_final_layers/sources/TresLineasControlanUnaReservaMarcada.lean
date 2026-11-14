import CambioDeUnaLineaEnLaReserva
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

theorem dos_esquinas_en_una_oblicua {n} (z e f : Cell n) (j : LineaReservable n) :
    (j∈lineasPropias (corners (z,e)).1 → j∈lineasPropias (corners (z,f)).1 → e.2=f.2) ∧
    (j∈lineasPropias (corners (z,e)).2 → j∈lineasPropias (corners (z,f)).2 → e.1=f.1) := by
  have bn:=e.2.isLt
  have cn:=f.2.isLt
  have dn:=z.2.isLt
  constructor <;> intro a b <;> simp only [lineasPropias,Finset.mem_insert,Finset.mem_singleton] at a b <;>
    rcases a with a|a <;> rcases b with b|b <;> subst j <;>
    simp [etiquetaD,etiquetaA,corners,Fin.ext_iff] at b <;> apply Fin.ext <;> omega

theorem masa_de_predicado_en_una_fibra {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (g : Cell n→Fin n) (P : Cell n→Prop) (misma : ∀ e f,P e→P f→g e=g f)
    (lineas : ∀ i,masaBajo w (fun e=>g e=i)≤1) : masaBajo w P≤1 := by
  by_cases exi : ∃ e,P e
  · obtain ⟨f,hf⟩:=exi
    exact (masaBajo_mono w pos (fun e he=>misma e f he hf)).trans (lineas (g f))
  · have empty (e):=show ¬P e from fun h=>exi ⟨e,h⟩
    simp [masaBajo,pesoCuando,empty]

theorem cambiar_una_reserva_cuesta_a_lo_sumo_tres {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (rows : ∀ i,masaBajo w (fun e=>e.1=i)≤1) (cols : ∀ i,masaBajo w (fun e=>e.2=i)≤1)
    (diag : ∀ j,masaBajo w (fun e=>j∈lineasPropias e)≤1) (z : Cell n)
    (ω ω' : LineaReservable n→Bool) (j : LineaReservable n) (off : ∀ i,i≠j→ω i=ω' i) :
    |masaMarcadaB1 w z ω-masaMarcadaB1 w z ω'|≤3 := by
  have a:=masa_de_predicado_en_una_fibra w pos Prod.snd _ (fun e f=> (dos_esquinas_en_una_oblicua z e f j).1) cols
  have b:=masa_de_predicado_en_una_fibra w pos Prod.fst _ (fun e f=> (dos_esquinas_en_una_oblicua z e f j).2) rows
  linarith only [cambio_marcado_por_tres_fibras w pos z ω ω' j off,a,b,diag j]

theorem cota_media_en_la_escala_de_B1 {n} (w : Cell n→ℝ) (pos : ∀ e,0≤w e) (z : Cell n)
    (hr : (∑ e : Cell n,if z.1=e.1 then w e else 0)≤1)
    (hc : (∑ e : Cell n,if z.2=e.2 then w e else 0)≤1) (τ : ℝ) (pτ : 0≤τ) (pe : τ≤1/8)
    (tam : 4≤∑ e : Cell n,w e) :
    τ^4*(∑ e : Cell n,w e)/4≤∑ ω : LineaReservable n→Bool,masaDeReserva τ ω*masaMarcadaB1 w z ω := by
  have base:=cota_media_marcada_de_B1 w pos z hr hc τ ⟨pτ,by linarith⟩
  apply le_trans _ base
  have a : (1/2:ℝ)≤(1-τ)^2:=by nlinarith only [mul_nonneg (show 0≤1/8-τ by linarith) (show 0≤15/8-τ by linarith)]
  have lb:=(mul_le_mul_of_nonneg_right a (show 0≤(∑ e : Cell n,w e)-2 by linarith))
  have h : (∑ e : Cell n,w e)/4≤(1-τ)^2*((∑ e : Cell n,w e)-2):=by linarith only [lb,tam]
  calc
    _ = τ^4*((∑ e : Cell n,w e)/4) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (mul_assoc _ _ _).symm

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_esquinas_en_una_oblicua
#print axioms ArticuloA.Historias.cambiar_una_reserva_cuesta_a_lo_sumo_tres
#print axioms ArticuloA.Historias.cota_media_en_la_escala_de_B1
