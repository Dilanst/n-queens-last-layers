import RetiradaDeReinas
import Mathlib.Data.Nat.Choose.Basic
namespace ArticuloA.Capas

theorem factor_agotado (n h : ℕ) (inside : h ≤ n) :
    falling n h = n.descFactorial h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change falling n h*(n-(h+1)+1) = _
    rw [Nat.descFactorial_succ,ih (by omega),show n-(h+1)+1=n-h by omega,Nat.mul_comm]

theorem factorial_capa (h : ℕ) : fac h = h.factorial := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change fac h*(h+1) = _
    rw [ih,Nat.factorial_succ,Nat.mul_comm]

/-- Section 3, lemma on removing h queens from a complete solution. -/
theorem retirada_binomial (n h : ℕ) (inside : h ≤ n) :
    n.choose h * count n n ≤ h.factorial * count n (n-h) := by
  have H := retirar n h inside
  rw [factor_agotado n h inside,Nat.descFactorial_eq_factorial_mul_choose,factorial_capa,
    Nat.pow_two,Nat.mul_assoc,Nat.mul_assoc] at H
  exact Nat.le_of_mul_le_mul_left H (Nat.factorial_pos _)
end ArticuloA.Capas
#print axioms ArticuloA.Capas.retirada_binomial
