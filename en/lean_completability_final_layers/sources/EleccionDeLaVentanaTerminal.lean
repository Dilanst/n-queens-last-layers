import RelojDelPrefijoRegular
open scoped NNReal
namespace ArticuloA.Historias
open RealFinita
noncomputable section

def restoDelReloj (N k : ℕ) := N/k+1

theorem ventana_final (n k : ℕ) (k2 : 2≤k) (kn : k≤n) :
    let N:=2*n-1
    let d:=restoDelReloj N k
    let T:=N-d
    T≤N ∧ (k:ℝ≥0)⁻¹≤fraccionAntes n T ∧
    (d:ℝ)≤4*(n:ℝ)/k ∧ 1-((T:ℝ)/N)≤2/(k:ℝ) ∧ N-T=d := by
  intro N d T
  have kN : k≤N := by dsimp [N]; omega
  have kp : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have NP : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have fit : d≤N := by
    have val:=Nat.div_mul_le_self N k
    have small : N/k*2≤N := (Nat.mul_le_mul_left _ k2).trans val
    dsimp [d,restoDelReloj]; omega
  have low : N≤k*d := (Nat.lt_mul_div_succ N (by omega : 0<k)).le
  have hi : d*k≤2*N := by
    dsimp [d,restoDelReloj]; rw [Nat.add_mul,one_mul]
    have aux:=Nat.div_mul_le_self N k; omega
  have eq : N-T=d := by dsimp [T]; omega
  have rd : (d:ℝ)*(k:ℝ)≤2*(N:ℝ) := by exact_mod_cast hi
  have rt : (T:ℝ)+(d:ℝ)=(N:ℝ) := by exact_mod_cast (show T+d=N by dsimp [T]; omega)
  have Nn : (N:ℝ)≤2*(n:ℝ) := by exact_mod_cast (show N≤2*n by dsimp [N]; omega)
  refine ⟨Nat.sub_le _ _,?_,(le_div_iff₀ kp).mpr (by linarith),?_,eq⟩
  · change (k:ℝ≥0)⁻¹ ≤ (↑(N-T):ℝ≥0)/N
    rw [eq]; change ((k:ℝ)⁻¹)≤(d:ℝ)/(N:ℝ)
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ kp NP).mpr (by simpa [mul_comm] using (show (N:ℝ)≤(k:ℝ)*d by exact_mod_cast low))
  · rw [show 1-(T:ℝ)/N=(d:ℝ)/N by field_simp; linarith]
    exact (div_le_div_iff₀ NP kp).mpr rd

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ventana_final
