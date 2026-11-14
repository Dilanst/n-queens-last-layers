import RangoDelRevelado
import DuenosDelNormalizador
import EleccionDelCorte
open scoped BigOperators
namespace ArticuloA.Revelado
noncomputable section
open Classical

theorem media_en_rango {α β : Type*} [DecidableEq α] (U : Finset α) (A : Finset β)
    (owners : β → Finset α) (sub : ∀ e∈A,owners e⊆U) (w : β → ℝ) (m : ℕ) (hm : m≤U.card) :
    (∑ T ∈ U.powersetCard m,∑ e ∈ A,if owners e⊆T then w e else 0)/((U.powersetCard m).card:ℝ) =
      ∑ e ∈ A,w e*((m.choose (owners e).card:ℝ)/(U.card.choose (owners e).card:ℝ)) := by
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl; intro e he
  rw [←supervivencia_en_un_rango U (owners e) (sub e he) m hm,←mul_div_assoc]
  congr 1
  rw [←Finset.sum_filter]
  simp [mul_comm]

theorem clases_en_rango {α β : Type*} [DecidableEq α] (U : Finset α) (A : Finset β)
    (owners : β → Finset α) (sub : ∀ e∈A,owners e⊆U) (w : β → ℝ) (nn : ∀ e∈A,0≤w e)
    (m : ℕ) (hm : m≤U.card) (pos : 0<U.card) :
    (∑ T ∈ U.powersetCard m,∑ e ∈ A,if owners e⊆T then w e else 0)/((U.powersetCard m).card:ℝ) ≤
      let z : ℝ := m/(U.card:ℝ)
      (∑ e ∈ A,w e)*z^4+(∑ e ∈ A,if (owners e).card≠4 then w e else 0)*z+
        (∑ e ∈ A,if owners e=∅ then w e else 0) := by
  rw [media_en_rango U A owners sub w m hm]
  let z : ℝ := m/(U.card:ℝ)
  have z0 : 0≤z := by dsimp [z]; positivity
  have z1 : z≤1 := (div_le_one (by exact_mod_cast pos)).mpr (by exact_mod_cast hm)
  calc
    _ ≤ ∑ e∈A,w e*z^(owners e).card := Finset.sum_le_sum (fun e he =>
      mul_le_mul_of_nonneg_left (cota_hipergeometrica m U.card _ hm (Finset.card_le_card (sub e he)) pos) (nn e he))
    _ ≤ _ := by
      rw [←media_normalizador U A owners sub w z]
      exact cota_tres_clases U A owners sub w nn z z0 z1
end
end ArticuloA.Revelado
#print axioms ArticuloA.Revelado.media_en_rango
#print axioms ArticuloA.Revelado.clases_en_rango
