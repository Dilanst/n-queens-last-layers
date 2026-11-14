import ColaDeUnObservableRealDetenido
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
/-- Choose the tilt before n. The two smallness conditions follow from the tolerance
and a bound on the jump divided by n. -/
theorem parametro_de_cola_inversa (B ε : ℝ) (bp : 0<B) (ep : 0<ε) :
    ∃ s : ℝ,0<s ∧ s*(2*B)≤1 ∧ 32*B^2*s≤ε := by
  let s:=min (1/(2*B)) (ε/(32*B^2))
  have b2 : 0<2*B := by positivity
  have b32 : 0<32*B^2 := by positivity
  exact ⟨s,lt_min (one_div_pos.mpr b2) (div_pos ep b32),
    (le_div_iff₀ b2).mp (min_le_left _ _),
    (mul_comm s _ ▸ (le_div_iff₀ b32).mp (min_le_right _ _))⟩

theorem exponente_del_conteo {n T : ℕ} (np : 0<n) (time : T≤2*n) {B ε s : ℝ}
    (sp : 0<s) (small : 32*B^2*s≤ε) :
    (T:ℝ)*((s/n)*(2*(B*n)))^2-(s/n)*(ε*n^2/2) ≤ -(s*ε/4)*(n:ℝ) := by
  have nr : (0:ℝ)<n := by exact_mod_cast np
  have scalar : (s/n)*(2*(B*n))=s*(2*B) := by field_simp; ring
  have cost : (s/n)*(ε*n^2/2)=s*ε*n/2 := by field_simp; ring
  have time' : (T:ℝ)≤2*(n:ℝ) := by exact_mod_cast time
  rw [scalar,cost]
  have top:=mul_le_mul_of_nonneg_right time' (sq_nonneg (s*(2*B)))
  have comp:=mul_le_mul_of_nonneg_right small (mul_nonneg sp.le nr.le)
  nlinarith only [top,comp]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.parametro_de_cola_inversa
#print axioms ArticuloA.Historias.exponente_del_conteo
