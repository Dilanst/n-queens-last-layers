import CambioInversoPonderado
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Ring
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def sumaCampo : SumLaw 𝕜 := ⟨0,(·+·),zero_add,add_comm,add_assoc⟩

private def presupuesto (M : 𝕜) (hM : 0 ≤ M) : WeightBudget (sumaCampo (𝕜:=𝕜)) where
  near t a b := |a-b| ≤ (t:𝕜)*M
  reflex := by intro a; simp
  symm := by intro t a b h; simpa only [abs_sub_comm b a] using h
  chain := by
    intro i j a b c h g
    calc |a-c| ≤ |a-b|+|b-c| := abs_sub_le _ _ _
         _ ≤ _ := add_le_add h g
         _ = _ := by rw [Nat.cast_add,add_mul]
  plus := by
    intro i j a b c d h g
    change |(a+c)-(b+d)| ≤ _
    have eq : (a+c)-(b+d) = (a-b)+(c-d) := by ring
    calc _ = _ := congrArg abs eq
         _ ≤ _ := abs_add_le _ _
         _ ≤ _ := add_le_add h g
         _ = _ := by rw [Nat.cast_add,add_mul]
  weaken := by
    intro i j a b ij h
    exact h.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ij) hM)

theorem corte_con_signo {n t} {p q : Placement n} (path : TerminalPath p t q)
    (w : Cell n → 𝕜) (M : 𝕜) (hM : 0 ≤ M) (cap : ∀ z, |w z| ≤ M) :
    |totalInverso sumaCampo w p - totalInverso sumaCampo w q| ≤ 4*(n:𝕜)*t*M := by
  have H := corte_inverso_ponderado sumaCampo (presupuesto M hM) w (by
    intro z; simpa [presupuesto,sumaCampo] using cap z) path
  change _ ≤ ((4*n*t:ℕ):𝕜)*M at H
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using H
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.corte_con_signo
