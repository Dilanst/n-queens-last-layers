import RetiradaBinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
namespace ArticuloA.Capas
noncomputable section

theorem log_capa_por_retirada (n h : ℕ) (hn : 0<n) (rango : 2*h≤n) (qpos : 0<count n n) :
    Real.log (count n n) + h*Real.log n - h*Real.log 2 - 2*Real.log h.factorial
      ≤ Real.log (count n (n-h)) := by
  have nh : h≤n := by omega
  have half : (n:ℝ)/2 ≤ ((n+1-h:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : h≤n+1),Nat.cast_add,Nat.cast_one]
    have H : (2:ℝ)*h≤n := by exact_mod_cast rango
    linarith
  have desc := Nat.pow_sub_le_descFactorial n h
  rw [Nat.descFactorial_eq_factorial_mul_choose] at desc
  have bound : ((n:ℝ)/2)^h ≤ h.factorial*(n.choose h:ℝ) :=
    (pow_le_pow_left₀ (by positivity) half h).trans (by exact_mod_cast desc)
  have retirar : (n.choose h:ℝ)*(count n n:ℝ) ≤ h.factorial*(count n (n-h):ℝ) :=
    by exact_mod_cast retirada_binomial n h nh
  have main : ((n:ℝ)/2)^h*(count n n:ℝ) ≤ (h.factorial:ℝ)^2*(count n (n-h):ℝ) := calc
    _ ≤ ((h.factorial:ℝ)*(n.choose h:ℝ))*(count n n:ℝ) := mul_le_mul_of_nonneg_right bound (by positivity)
    _ = (h.factorial:ℝ)*((n.choose h:ℝ)*(count n n:ℝ)) := mul_assoc _ _ _
    _ ≤ (h.factorial:ℝ)*((h.factorial:ℝ)*(count n (n-h):ℝ)) := mul_le_mul_of_nonneg_left retirar (by positivity)
    _ = _ := by ring
  have N : 0<(n:ℝ) := by exact_mod_cast hn
  have Q : 0<(count n n:ℝ) := by exact_mod_cast qpos
  have F : 0<(h.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos h
  have positive : 0<((n:ℝ)/2)^h*(count n n:ℝ) := by positivity
  have layer : 0<(count n (n-h):ℝ) := by
    by_contra! he
    exact (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) he)) (positive.trans_le main)
  have logs := Real.log_le_log positive main
  rw [Real.log_mul (by positivity) Q.ne',Real.log_pow,Real.log_div N.ne' (by norm_num),
    Real.log_mul (by positivity) layer.ne',Real.log_pow] at logs
  push_cast at logs
  linarith

theorem cancelacion_de_borde (n h : ℕ) (hn : 0<n) (rango : 2*h≤n) (qpos : 0<count n n)
    (s s₁ E : ℝ) (borde : (n:ℝ)*(s-s₁)≤2*h*Real.log n+E) :
    ((n-h:ℕ):ℝ)*Real.log n + n*s - Real.log (count n (n-h)) ≤
      n*Real.log n + n*s₁ - Real.log (count n n) + E + h*Real.log 2 + 2*Real.log h.factorial := by
  rw [Nat.cast_sub (by omega : h≤n)]
  linarith [log_capa_por_retirada n h hn rango qpos]
end
end ArticuloA.Capas
#print axioms ArticuloA.Capas.log_capa_por_retirada
#print axioms ArticuloA.Capas.cancelacion_de_borde
