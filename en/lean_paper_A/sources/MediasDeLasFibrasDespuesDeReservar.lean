import UnaMismaReservaEnB1YEnElProcesoG
import ColaParaUnSorteoDeOblicuas
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

/-- The weights may first be restricted to any fixed set of squares. -/
def retenidaPor {n} (w : Cell n→ℝ) (S : Cell n→Finset (LineaReservable n))
    (ω : LineaReservable n→Bool) : ℝ :=
  ∑ e : Cell n,if acuerdoDeReserva ∅ (S e) ω then w e else 0

theorem media_de_masa_retenida {n} (τ : ℝ) (w : Cell n→ℝ)
    (S : Cell n→Finset (LineaReservable n)) (j : ℕ) (todas : ∀ e,(S e).card=j) :
    mediaCubo τ (retenidaPor w S)=(1-τ)^j*(∑ e : Cell n,w e) := by
  unfold mediaCubo retenidaPor
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have one:=probabilidad_de_un_patron_de_reserva τ (∅ : Finset (LineaReservable n)) (S e) (by simp)
  simp only [Finset.card_empty,pow_zero,one_mul,todas] at one
  rw [←one,Finset.sum_mul]
  apply Finset.sum_congr (by ext ω; simp)
  intro ω _
  by_cases ok : acuerdoDeReserva ∅ (S e) ω <;> simp [ok]

theorem media_tras_las_dos_oblicuas {n} (τ : ℝ) (w : Cell n→ℝ) :
    mediaCubo τ (retenidaPor w lineasPropias)=(1-τ)^2*(∑ e : Cell n,w e) :=
  media_de_masa_retenida τ w lineasPropias 2 son_dos_lineas_propias

theorem media_al_dejar_libre_la_oblicua_propia {n} (τ : ℝ) (w : Cell n→ℝ)
    (otra : Cell n→LineaReservable n) :
    mediaCubo τ (retenidaPor w (fun e=>{otra e}))=(1-τ)*(∑ e : Cell n,w e) := by
  simpa only [pow_one] using media_de_masa_retenida τ w (fun e=>{otra e}) 1 (by simp)

theorem retener_las_dos_es_la_mascara_fisica {n} (w : Cell n→ℝ) (ω : LineaReservable n→Bool) :
    retenidaPor w lineasPropias ω = ∑ e : Cell n,if quedaTrasReserva ω e then w e else 0 := by
  unfold retenidaPor
  apply Finset.sum_congr rfl
  intro e _
  simp [acuerdoDeReserva,lineasPropias,quedaTrasReserva]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_tras_las_dos_oblicuas
#print axioms ArticuloA.Historias.media_al_dejar_libre_la_oblicua_propia
#print axioms ArticuloA.Historias.retener_las_dos_es_la_mascara_fisica
