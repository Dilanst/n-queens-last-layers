import CandidatasEnUnRango
import EntropiaProyectadaAlTablero
open scoped BigOperators
namespace ArticuloA.Revelado
noncomputable section
open Classical

def porSubconjunto {α β : Type*} [DecidableEq α] (A : Finset β) (owners : β → Finset α)
    (w : β → ℝ) (T : Finset α) := ∑ e∈A, if owners e⊆T then w e else 0

def porRango {α : Type*} (U : Finset α) (m : ℕ) (v : Finset α → ℝ) :=
  (∑ T ∈ U.powersetCard m, v T)/((U.powersetCard m).card:ℝ)

/-- Uniform rank and posterior set. The exceptional masses must be proved on the chosen board. -/
theorem suma_de_log_por_pieza {α β : Type*} [DecidableEq α] (U : Finset α) (A : Finset β)
    (owners : β → Finset α) (sub : ∀ e∈A,owners e⊆U) (w : β → ℝ) (nn : ∀ e∈A,0≤w e)
    {W c : ℝ} (wpos : 0<W) (c0 : 0≤c) (D : 0<U.card) (total : ∑ e∈A,w e=W)
    (ex : (∑ e∈A,if (owners e).card≠4 then w e else 0) ≤ c*W/(U.card+1))
    (special : (∑ e∈A,if owners e=∅ then w e else 0) ≤ c*W/(U.card+1)^2)
    (marcada : ∃ e∈A,owners e=∅ ∧ 0<w e) :
    ∑ m∈Finset.range (U.card+1),porRango U m (fun T => Real.log (porSubconjunto A owners w T)) ≤
      ((U.card:ℝ)+1)*Real.log W-4*((U.card:ℝ)+1)+4+(4+6*c)*(Rangos.corte U.card D:ℝ) := by
  let v := porSubconjunto A owners w
  let Y := fun m => porRango U m v
  have cardpos (m) (hm : m≤U.card) : 0<((U.powersetCard m).card:ℝ) := by
    rw [Finset.card_powersetCard]; exact_mod_cast Nat.choose_pos hm
  have good (T : Finset α) : 0<v T := by
    obtain ⟨e,he,emp,pos⟩ := marcada
    apply Finset.sum_pos' (fun j hj => by split <;> simp [nn j hj])
    exact ⟨e,he,by simpa [emp] using pos⟩
  have yp (m) (hm : m≤U.card) : 0<Y m := by
    apply div_pos _ (cardpos m hm)
    apply Finset.sum_pos (fun i _ => good i)
    exact Finset.card_pos.mp (by exact_mod_cast cardpos m hm)
  have cls (m) (hm : m≤U.card) :
      Y m/W≤((m:ℝ)/U.card)^4+c*((m:ℝ)/U.card)/(U.card+1)+c/(U.card+1)^2 := by
    have t := clases_en_rango U A owners sub w nn m hm D
    rw [total] at t
    apply (div_le_iff₀ wpos).mpr
    calc
      _ ≤ _ := t
      _ ≤ W*((m:ℝ)/U.card)^4+(c*W/(U.card+1))*(m/(U.card:ℝ))+c*W/(U.card+1)^2 :=
        add_le_add (add_le_add_left (mul_le_mul_of_nonneg_right ex (by positivity)) _) special
      _ = _ := by ring
  have jensen (m) (hm : m≤U.card) : porRango U m (fun T => Real.log (v T))≤Real.log (Y m) := by
    let S := U.powersetCard m
    have nz : (S.card:ℝ)≠0 := (cardpos m hm).ne'
    have norm : ∑ _T∈S,((S.card:ℝ)⁻¹)=1 := by simp [nz]
    have prod (f : Finset α→ℝ) : ∑ T∈S,((S.card:ℝ)⁻¹)*f T=porRango U m f := by
      rw [←Finset.mul_sum]; simp [porRango,S,div_eq_mul_inv,mul_comm]
    have J := Historias.jensen_normalizador S (fun _ => (S.card:ℝ)⁻¹) v (Y m)
      (fun _ _ => by positivity) (fun i _ => good i) (yp m hm) norm (prod v).le
    simpa only [prod] using J
  exact (Finset.sum_le_sum (fun m hm => jensen m (by have := Finset.mem_range.mp hm; omega))).trans
    (Rangos.normalizadores_con_corte D c0 wpos Y yp cls)
end
end ArticuloA.Revelado
#print axioms ArticuloA.Revelado.suma_de_log_por_pieza
