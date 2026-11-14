import GronwallConInnovaciones
import Mathlib.Data.Complex.Exponential
namespace ArticuloA.Seguimiento
theorem antes_de_salida (E : ℕ → ℝ) (T : ℕ) (g L θ : ℝ) (hg : 0 ≤ g) (hL : 0 ≤ L)
    (bound : ∀ t ≤ T, E t + 1 ≤ (g+1)*(1+L)^t)
    (margin : (g+1)*Real.exp (T*L) < θ) : ∀ t ≤ T, E t < θ := by
  intro t ht
  have A : 1+L ≤ Real.exp L := by simpa [add_comm] using Real.add_one_le_exp L
  have B := pow_le_pow_left₀ (by linarith : 0 ≤ 1+L) A t
  have eq : (Real.exp L)^t = Real.exp (t*L) := (Real.exp_nat_mul L t).symm
  rw [eq] at B
  have C := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show (t:ℝ) ≤ T by exact_mod_cast ht) hL)
  have D := mul_le_mul_of_nonneg_left (B.trans C) (by linarith : 0 ≤ g+1)
  linarith [bound t ht]
end ArticuloA.Seguimiento
#print axioms ArticuloA.Seguimiento.cota_de_trayectoria
#print axioms ArticuloA.Seguimiento.antes_de_salida
