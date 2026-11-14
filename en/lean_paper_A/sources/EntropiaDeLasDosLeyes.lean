import PesoDeUnaRama
import Mathlib.Data.Nat.Choose.Basic
open scoped BigOperators
namespace ArticuloA.Historias
noncomputable section
open Classical
variable {n q : ℕ}

def masaPalabra (n q : ℕ) : ℝ :=
  (q.factorial:ℝ) * ((2*n-1-q).factorial:ℝ) / ((2*n-1).factorial:ℝ)

theorem palabra_uniforme (hq : q≤2*n-1) : masaPalabra n q=((2*n-1).choose q:ℝ)⁻¹ := by
  have ch : ((2*n-1).choose q:ℝ) * (q.factorial:ℝ) * ((2*n-1-q).factorial:ℝ) =
      ((2*n-1).factorial:ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hq
  have h1 : ((2*n-1).choose q:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hq).ne'
  have h2 : ((2*n-1).factorial:ℝ) ≠ 0 := by positivity
  unfold masaPalabra
  field_simp
  linarith only [ch, mul_comm ((q.factorial:ℝ)*((2*n-1-q).factorial:ℝ)) ((2*n-1).choose q:ℝ)]

/-- Sequential colour quotas for a prescribed word, including its first letter. -/
def productoCuotas : List Bool → ℝ
  | [] => 1
  | b::bs => (((b::bs).count b : ℝ) / (b::bs).length) * productoCuotas bs

theorem cuotas_factoriales (bs : List Bool) :
    productoCuotas bs = ((bs.count true).factorial:ℝ)*((bs.count false).factorial:ℝ)/(bs.length.factorial:ℝ) := by
  induction bs with
  | nil => simp [productoCuotas]
  | cons b bs ih =>
    cases b <;> simp [productoCuotas,ih,List.count_cons,Nat.factorial_succ,div_eq_mul_inv,mul_inv_rev] <;> ring

def masaRamaCon (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (D : Historia n q → Indice n → ℝ) : ℝ :=
  masaPalabra n q * ∏ t, peso H u t / D H t

private theorem peso_pos (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j) (t : Indice n) :
    0 < peso H u t := by
  unfold peso pesoDe
  exact Finset.prod_pos (fun i _ => hu i _)

theorem masaRamaCon_pos (D : Historia n q → Indice n → ℝ) (hD : ∀ H t,0<D H t) (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j) :
    0<masaRamaCon H u D := by
  have word : 0<masaPalabra n q := by unfold masaPalabra; positivity
  exact mul_pos word (Finset.prod_pos (fun t _ => div_pos (peso_pos H u hu t) (hD H t)))

theorem log_por_rama (D : Historia n q → Indice n → ℝ) (hD : ∀ H t,0<D H t) (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j)
    (hn : 0<count n q) :
    Real.log (proba n q / masaRamaCon H u D) =
      (∑ t, Real.log (D H t)) - (∑ i, ∑ j, Real.log (u i j)) -
      Real.log (count n q) - Real.log q.factorial - 4*Real.log (2*n-1-q).factorial := by
  have wc : (count n q:ℝ)≠0 := by exact_mod_cast hn.ne'
  have fac (k : ℕ) : (k.factorial:ℝ)≠0 := by positivity
  have pc : (∏ t,peso H u t) ≠ 0 := (Finset.prod_pos (fun t _ => peso_pos H u hu t)).ne'
  have nc : (∏ t,D H t) ≠ 0 := (Finset.prod_pos (fun t _ => hD H t)).ne'
  have wpos : masaPalabra n q ≠ 0 := by unfold masaPalabra; positivity
  have nonzero : proba n q ≠ 0 := by
    rw [proba,card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]
    exact inv_ne_zero (mul_ne_zero wc (mul_ne_zero (pow_ne_zero _ (fac _)) (fac _)))
  rw [Real.log_div nonzero (masaRamaCon_pos D hD H u hu).ne',proba,Real.log_inv,card_historias,
    Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow,Real.log_mul wc (mul_ne_zero (pow_ne_zero _ (fac _)) (fac _)),
    Real.log_mul (pow_ne_zero _ (fac _)) (fac _),Real.log_pow,masaRamaCon,Finset.prod_div_distrib,
    Real.log_mul wpos (div_ne_zero pc nc),Real.log_div pc nc,producto_de_pesos,
    Real.log_prod _ _ (fun i _ => (Finset.prod_pos (fun j _ => hu i j)).ne'),
    Real.log_prod _ _ (fun t _ => (hD H t).ne'),masaPalabra,
    Real.log_div (mul_ne_zero (fac _) (fac _)) (fac _),Real.log_mul (fac _) (fac _)]
  simp_rw [Real.log_prod _ _ (fun j _ => (hu _ j).ne')]
  ring

theorem identidad_con_normalizadores (D : Historia n q → Indice n → ℝ) (hD : ∀ H t,0<D H t) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j)
    (hn : 0<count n q) :
    ∑ H : Historia n q, proba n q * Real.log (proba n q / masaRamaCon H u D) =
      (∑ H : Historia n q, proba n q * ∑ t, Real.log (D H t)) -
      (∑ i, ∑ j, Real.log (u i j)) - Real.log (count n q) -
      Real.log q.factorial - 4*Real.log (2*n-1-q).factorial := by
  have norm : ∑ _ : Historia n q, proba n q = 1 := by
    have nt : (Fintype.card (Historia n q):ℝ) ≠ 0 := by
      rw [card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]
      exact mul_ne_zero (by exact_mod_cast hn.ne') (by positivity)
    simp only [proba,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_inv_cancel₀ nt]
  simp_rw [log_por_rama D hD _ u hu hn,mul_sub,Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul,norm,one_mul]

theorem identidad_entropica (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j)
    (hn : 0<count n q) :
    ∑ H : Historia n q, proba n q * Real.log (proba n q / masaRamaCon H u (fun B => normalizador B u)) =
      (∑ H : Historia n q, proba n q * ∑ t, Real.log (normalizador H u t)) -
      (∑ i, ∑ j, Real.log (u i j)) - Real.log (count n q) -
      Real.log q.factorial - 4*Real.log (2*n-1-q).factorial :=
  identidad_con_normalizadores _ (fun B t => positivo B u hu t) u hu hn
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.palabra_uniforme
#print axioms ArticuloA.Historias.identidad_entropica
