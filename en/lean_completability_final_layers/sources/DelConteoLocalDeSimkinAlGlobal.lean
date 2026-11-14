import MarginalesAdmisiblesDelPerfilLleno
import ConteoDePrimerOrdenSinVecindades
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Limites Perfil
open scoped Topology

def raizDelConteo (a : ℕ→ℕ) (n : ℕ) : ℝ := (a n:ℝ)^((n:ℝ)⁻¹)/(n:ℝ)

/-- The input is the lower exponential growth of a set of full placements inside
a neighborhood. Its finite membership is checked using the legal layer. -/
theorem desde_el_liminf_local (s : ℝ) (S : (n : ℕ)→Finset (Placement n))
    (sub : ∀ n,S n⊆nivel n n)
    (localBound : Real.exp s≤liminf (raizDelConteo (fun n => (S n).card)) atTop) :
    CotaDePrimerOrden s := by
  intro ε ep
  let a:=fun n => (S n).card
  have low : IsBoundedUnder (·≥·) atTop (raizDelConteo a) :=
    by
      refine ⟨0,?_⟩
      change ∀ᶠ n : ℕ in atTop,0≤raizDelConteo a n
      exact Eventually.of_forall (fun n => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (a n)) _) (Nat.cast_nonneg n))
  have less : Real.exp (s-ε)<liminf (raizDelConteo a) atTop :=
    (Real.exp_lt_exp.mpr (sub_lt_self _ ep)).trans_le localBound
  filter_upwards [eventually_lt_of_lt_liminf less low,eventually_ge_atTop 1] with n loc hn
  have np : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have pos : 0<n := by omega
  have one : Real.exp (s-ε)*(n:ℝ)<(a n:ℝ)^((n:ℝ)⁻¹) := (lt_div_iff₀ np).mp loc
  have lift := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le np.le) one.le n
  rw [Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) pos.ne'] at lift
  have upper : a n≤count n n := (Finset.card_le_card (sub n)).trans_eq (cardinal_nivel n n)
  have val : (Real.exp (s-ε)*(n:ℝ))^n ≤ (count n n:ℝ) :=
    lift.trans (by exact_mod_cast upper)
  have bd:=Real.log_le_log (pow_pos (mul_pos (Real.exp_pos _) np) n) val
  rw [Real.log_pow,Real.log_mul (Real.exp_pos _).ne' np.ne',Real.log_exp] at bd
  linarith

/-- A fixed positive radius suffices. The neighborhood selection itself and
Simkin's local theorem are explicit external inputs. -/
theorem primer_orden_para_el_perfil {P p b}
    (h : EulerFisica P p 0 b)
    (S : (n : ℕ)→Finset (Placement n)) (sub : ∀ n,S n⊆nivel n n)
    (simkin : admisibleParaConteo P → Real.exp (valorCentrado P)≤
      liminf (raizDelConteo (fun n => (S n).card)) atTop) :
    CotaDePrimerOrden (valorCentrado P) :=
  desde_el_liminf_local _ S sub (simkin (perfil_lleno_admisible h))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.desde_el_liminf_local
#print axioms ArticuloA.Historias.primer_orden_para_el_perfil
