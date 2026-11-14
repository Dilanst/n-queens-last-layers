import EntropiaDeLasDosLeyes
open scoped BigOperators
namespace ArticuloA.Historias
noncomputable section
open Classical

theorem log_suma_en_fibra {ι : Type*} [Fintype ι] (p v : ι → ℝ) (a b : ℝ)
    (hp : ∀ i,0<p i) (hv : ∀ i,0<v i) (ha : 0<a) (hb : 0<b)
    (sumaP : ∑ i,p i=a) (sumaV : ∑ i,v i≤b) :
    a*Real.log (a/b) ≤ ∑ i,p i*Real.log (p i/v i) := by
  have point (i : ι) : p i*Real.log (a/b) + p i - (a/b)*v i ≤ p i*Real.log (p i/v i) := by
    have frac := div_pos (mul_pos (div_pos ha hb) (hv i)) (hp i)
    have ineq := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos frac) (hp i).le
    rw [Real.log_div (mul_pos (div_pos ha hb) (hv i)).ne' (hp i).ne',Real.log_mul (div_pos ha hb).ne' (hv i).ne'] at ineq
    have alg : p i*((a/b*v i)/p i -1) = a/b*v i-p i := by
      rw [mul_sub,mul_one,mul_comm (p i) ((a/b*v i)/p i),div_mul_cancel₀ _ (hp i).ne']
    rw [alg] at ineq
    rw [Real.log_div (hp i).ne' (hv i).ne']
    linarith
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,sumaP] at sum
  have corr := mul_le_mul_of_nonneg_left sumaV (div_pos ha hb).le
  rw [div_mul_cancel₀ _ hb.ne'] at corr
  linarith

/-- Jensen allows zero probability atoms, but needs strictly positive normalizers. -/
theorem jensen_normalizador {ι : Type*} (S : Finset ι) (p v : ι → ℝ) (M : ℝ)
    (hp : ∀ i∈S,0≤p i) (hv : ∀ i∈S,0<v i) (hm : 0<M)
    (norm : ∑ i∈S,p i=1) (upper : ∑ i∈S,p i*v i≤M) :
    ∑ i∈S,p i * Real.log (v i) ≤ Real.log M := by
  have point (i : ι) (hi : i∈S) : p i*Real.log (v i) ≤ p i * (Real.log M + v i/M - 1) := by
    have bound := Real.log_le_sub_one_of_pos (div_pos (hv i hi) hm)
    rw [Real.log_div (hv i hi).ne' hm.ne'] at bound
    exact mul_le_mul_of_nonneg_left (by linarith) (hp i hi)
  have all := Finset.sum_le_sum point
  simp_rw [mul_sub,mul_add,mul_one,mul_div_assoc'] at all
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_div,norm,one_mul] at all
  have le := (div_le_one hm).mpr upper
  linarith

theorem divergencia_del_tablero {n q : ℕ} (hn : 0<count n q)
    (v : Historia n q → ℝ) (r : Tablero n q → ℝ)
    (hv : ∀ H,0<v H) (hr : ∀ P,0<r P)
    (dom : ∀ P, (∑ d : Decoracion P,v ⟨P,d⟩) ≤ r P) :
    (∑ P : Tablero n q, (count n q:ℝ)⁻¹ * Real.log ((count n q:ℝ)⁻¹/r P)) ≤
    ∑ H : Historia n q, proba n q * Real.log (proba n q/v H) := by
  have hc : 0<(count n q:ℝ) := by exact_mod_cast hn
  have ph : 0<proba n q := by
    rw [proba,card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]
    exact inv_pos.mpr (mul_pos hc (by positivity))
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun P _ => log_suma_en_fibra _ _ _ _ (fun _ => ph)
    (fun d => hv ⟨P,d⟩) (inv_pos.mpr hc) (hr P) (proyeccion n q P) (dom P))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.log_suma_en_fibra
#print axioms ArticuloA.Historias.divergencia_del_tablero
