import GronwallRealDeSalida
import Mathlib.Algebra.Order.BigOperators.Group.Finset
open scoped BigOperators
namespace ArticuloA.Seguimiento
noncomputable section
open Classical

/-- For first-exit paths, drift bounds are needed only strictly before the exit step. -/
theorem ruido_en_primera_salida {ι : Type*} (E : ℕ → ℝ) (D M : ι → ℕ → ℝ)
    (s T : ℕ) (sT : s≤T) (g L umbral : ℝ) (g0 : 0≤g) (L0 : 0≤L)
    (margin : (g+1)*Real.exp (T*L)<umbral)
    (drift : ∀ i t,t<s → |D i t|≤L*(E t+1))
    (coord : ∀ t≤s,∃ i,E t ≤ |M i t + ∑ j ∈ Finset.range t,D i j|)
    (salida : umbral≤E s) : ∃ i t,t≤s ∧ g < |M i t| := by
  by_contra! small
  have ruido (i) (t) (ht : t≤s) : |M i t|≤g := small i t ht
  have lev := cota_de_trayectoria E D M s g L L0 drift ruido coord
  have st : (s:ℝ)≤T := by exact_mod_cast sT
  have mg : (g+1)*Real.exp (s*L)<umbral :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right st L0))
      (by linarith)).trans_lt margin
  exact (not_lt.mpr salida) (antes_de_salida E s g L umbral g0 L0 lev mg s le_rfl)

/-- The atom weights need not be independent across coordinates or times. -/
theorem masa_de_salida {Ω ι : Type*} [Fintype ι] (esp : Finset Ω) (p : Ω → ℝ)
    (nn : ∀ ω ∈ esp,0≤p ω) (bad : Ω → Prop) (M : Ω → ι → ℕ → ℝ) (T : ℕ) (g b : ℝ)
    (testigo : ∀ ω ∈ esp,bad ω → ∃ i t,t≤T ∧ g < |M ω i t|)
    (colas : ∀ i t,t≤T → ∑ ω ∈ esp,(if g < |M ω i t| then p ω else 0) ≤ b) :
    ∑ ω ∈ esp,(if bad ω then p ω else 0) ≤ (Fintype.card ι:ℝ)*(T+1)*b := by
  let s := (Finset.univ : Finset ι) ×ˢ Finset.range (T+1)
  let v := fun (j : ι × ℕ) (ω : Ω) => if g < |M ω j.1 j.2| then p ω else 0
  have pos (ω) (hw : ω∈esp) (j) : 0≤v j ω := by dsimp [v]; split <;> simp [nn ω hw]
  have le (ω) (hw : ω∈esp) : (if bad ω then p ω else 0)≤∑ j ∈ s,v j ω := by
    by_cases badω : bad ω
    · obtain ⟨i,t,ht,ex⟩ := testigo ω hw badω
      have j : (i,t)∈s := Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (by omega)⟩
      have c := Finset.single_le_sum (fun j _ => pos ω hw j) j
      simpa [badω,v,ex] using c
    · simp only [badω,if_false]
      exact Finset.sum_nonneg (fun j _ => pos ω hw j)
  calc
    _ ≤ _ := Finset.sum_le_sum le
    _ = ∑ j ∈ s,∑ ω ∈ esp,v j ω := Finset.sum_comm
    _ ≤ ∑ _j ∈ s,b := Finset.sum_le_sum (fun j hj => colas j.1 j.2
      (by have H := Finset.mem_range.mp (Finset.mem_product.mp hj).2; omega))
    _ = _ := by simp [s,mul_assoc]
end
end ArticuloA.Seguimiento
#print axioms ArticuloA.Seguimiento.ruido_en_primera_salida
#print axioms ArticuloA.Seguimiento.masa_de_salida
