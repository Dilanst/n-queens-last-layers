import EulerEnFibrasSinConstanteLipschitz
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def nucleoFilaExtendida (C D A : ℝ→ℝ) (s : ℝ) := ∫ t in (0:ℝ)..1,C t*D (s-t)*A (s+t)
def filaPorEuler (C D A : ℝ→ℝ) (x b s : ℝ) := (x+b*nucleoFilaExtendida C D A s)⁻¹

theorem banda_del_nucleo_de_fila {C D A : ℝ→ℝ} {κ : ℝ} (kn : 0≤κ)
    (cC : Continuous C) (cD : Continuous D) (cA : Continuous A)
    (nn : ∀ t∈Icc (0:ℝ) 1,0≤C t) (masa : (∫ t in (0:ℝ)..1,C t)=1)
    (d : ∀ t,κ≤D t ∧ D t≤1) (a : ∀ t,κ≤A t ∧ A t≤1) (s : ℝ) :
    κ^2≤nucleoFilaExtendida C D A s ∧ nucleoFilaExtendida C D A s≤1 := by
  let f:=fun t=>C t*D (s-t)*A (s+t)
  have cf : Continuous f := (cC.mul (cD.comp (continuous_const.sub continuous_id))).mul
    (cA.comp (continuous_const.add continuous_id))
  have lo:=intervalIntegral.integral_mono_on (μ:=volume) zero_le_one (cC.mul continuous_const |>.intervalIntegrable _ _)
    (cf.intervalIntegrable _ _) (f:=fun t=>C t*κ^2) (g:=f) (fun t ht=>by
      dsimp [f]; rw [sq,mul_assoc (C t) (D _) (A _)]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul (d _).1 (a _).1 kn (kn.trans (d _).1)) (nn t ht))
  have hi:=intervalIntegral.integral_mono_on (μ:=volume) zero_le_one (cf.intervalIntegrable _ _) (cC.intervalIntegrable _ _)
    (f:=f) (g:=C) (fun t ht=>by
      dsimp [f]; rw [mul_assoc]; apply mul_le_of_le_one_right (nn t ht)
      exact (mul_le_mul (d _).2 (a _).2 (kn.trans (a _).1) zero_le_one).trans_eq (one_mul _))
  rw [intervalIntegral.integral_mul_const,masa,one_mul] at lo
  rw [masa] at hi
  exact ⟨lo,hi⟩

theorem continuidad_del_nucleo_extendido {C D A : ℝ→ℝ} (cC : Continuous C) (cD : Continuous D)
    (cA : Continuous A) : Continuous (nucleoFilaExtendida C D A) := by
  have hf : Continuous (Function.uncurry (fun s t : ℝ=>C t*D (s-t)*A (s+t))) :=
    ((cC.comp continuous_snd).mul (cD.comp (continuous_fst.sub continuous_snd))).mul
      (cA.comp (continuous_fst.add continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume) (a₀:=(0:ℝ))
    hf (continuous_const (y:=(1:ℝ)))

theorem fila_extendida_resuelve_euler {C D A : ℝ→ℝ} {x b κ : ℝ}
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ)
    (banda : ∀ s,κ^2≤nucleoFilaExtendida C D A s ∧ nucleoFilaExtendida C D A s≤1)
    (cC : Continuous C) (cD : Continuous D) (cA : Continuous A) :
    Continuous (filaPorEuler C D A x b) ∧ ∀ s,
      1/(x+b)≤filaPorEuler C D A x b s ∧ filaPorEuler C D A x b s≤1/(x+b*κ^2) ∧
      filaPorEuler C D A x b s*(x+b*nucleoFilaExtendida C D A s)=1 := by
  have lp : 0<x+b*κ^2 := add_pos_of_nonneg_of_pos xn (mul_pos bp (sq_pos_of_pos kp))
  have low s := add_le_add_right (mul_le_mul_of_nonneg_left (banda s).1 bp.le) x
  have pos s : 0<x+b*nucleoFilaExtendida C D A s := lp.trans_le (by linarith only [low s])
  refine ⟨(continuous_const.add (continuous_const.mul (continuidad_del_nucleo_extendido cC cD cA))).inv₀
    (fun s=>(pos s).ne'),?_⟩
  intro s
  have upper:=mul_le_mul_of_nonneg_left (banda s).2 bp.le
  unfold filaPorEuler; simp only [one_div]
  exact ⟨(inv_le_inv₀ (by linarith) (pos s)).mpr (by linarith),
    (inv_le_inv₀ (pos s) lp).mpr (by linarith only [low s]),inv_mul_cancel₀ (pos s).ne'⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.banda_del_nucleo_de_fila
#print axioms ArticuloA.Historias.continuidad_del_nucleo_extendido
#print axioms ArticuloA.Historias.fila_extendida_resuelve_euler
