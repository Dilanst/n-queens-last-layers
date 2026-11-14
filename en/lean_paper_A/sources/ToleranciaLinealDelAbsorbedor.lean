import RegularidadDeE2HastaElCorte
open scoped NNReal
namespace ArticuloA.Historias
open RealFinita
noncomputable section

theorem tolerancia_para_la_raiz (D piso γ : ℝ≥0) (fl : 0<piso) (gp : 0<γ) :
    ∃ ε : ℝ≥0,0<ε ∧ ε≤piso ∧ ∃ N : ℕ,∀ n≥N,∀ T≤2*n,
      (T:ℝ≥0)*(D*(ε*n+1)/n)≤γ*n/2 := by
  let ε:=min piso (γ/(8*(D+1)))
  have dp : 0<8*(D+1) := by positivity
  have ep : 0<ε := lt_min fl (div_pos gp dp)
  obtain ⟨N,nlarge⟩:=exists_nat_gt ((8*(D+1)/γ:ℝ≥0):ℝ)
  refine ⟨ε,ep,min_le_left _ _,max 1 N,?_⟩
  intro n hn T tT
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
  have e := (le_div_iff₀ dp).mp (min_le_right piso (γ/(8*(D+1))))
  have er : ε*(8*D)≤γ := (mul_le_mul_left' (show 8*D≤8*(D+1) by gcongr; exact le_add_of_nonneg_right (zero_le _)) ε).trans e
  have large : 8*(D+1)/γ≤(n:ℝ≥0) := NNReal.coe_le_coe.mp (nlarge.le.trans (by exact_mod_cast (by omega : N≤n)))
  have lr := (div_le_iff₀ gp).mp large
  have be : 8*D≤(n:ℝ≥0)*γ := (show 8*D≤8*(D+1) by gcongr; exact le_add_of_nonneg_right (zero_le _)).trans lr
  have t : (T:ℝ≥0)≤2*n := by exact_mod_cast tT
  calc
    _ ≤ (2*n)*(D*(ε*n+1)/n) := mul_le_mul_right' t _
    _ = 2*D*ε*n+2*D := by field_simp; ring
    _ ≤ γ*n/2 := by
      have eR:=NNReal.coe_le_coe.mpr (mul_le_mul_right' er (n:ℝ≥0))
      have bR:=NNReal.coe_le_coe.mpr be
      change ((2*D*ε*n+2*D:ℝ≥0):ℝ)≤((γ*n/2:ℝ≥0):ℝ)
      push_cast at *; nlinarith only [eR,bR]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tolerancia_para_la_raiz
