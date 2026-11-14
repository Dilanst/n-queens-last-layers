import BalanceEscaladoDeLaMalla
import L1DeLaFamiliaCanonica
open Set MeasureTheory Filter
open scoped NNReal Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem integral_fisica_no_negativa (p : FactoresContinuos) (i : Fin 4) (t : ℝ) (mem : t∈rangoF i) :
    0 ≤ integralFisica p i t := by
  have non (x y : ℝ) : 0≤pesoContinuo p x y := by unfold pesoContinuo; positivity
  fin_cases i
  · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => non _ _)
  · exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => non _ _)
  · change t∈Icc (-1:ℝ) 1 at mem
    apply intervalIntegral.integral_nonneg_of_forall _ (fun _ => non _ _)
    exact sub_nonneg.mpr (abs_le.mpr mem)
  · change t∈Icc (0:ℝ) 2 at mem
    apply intervalIntegral.integral_nonneg_of_forall _ (fun _ => non _ _)
    apply sub_nonneg.mpr
    exact abs_le.mpr ⟨by linarith [mem.1],by linarith [mem.2]⟩

def EulerPuntualDeRama (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) : Prop :=
  ∀ x∈Icc (0:ℝ) (1/2:ℝ),∀ i,∀ t∈rangoF i,
    b x*integralFisica (p x) i t=1-holguraLinea (p x) x.toNNReal i t

theorem balance_de_la_rama_puntual {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b) :
    ∃ C : ℝ≥0,∀ h : ℕ,∀ᶠ n : ℕ in atTop,BalanceMalla n h (p ((h:ℝ)/n)) C := by
  let C:ℝ≥0:=⟨4*(4*M^3*L)/κ^4,by have := rama.lp; have := rama.m1; positivity⟩
  refine ⟨C,?_⟩
  intro h
  filter_upwards [eventually_ge_atTop (2*h+1)] with n big
  have np : 0<n := by omega
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  let x:ℝ:=(h:ℝ)/n
  have xnn : 0≤x := by dsimp [x]; positivity
  have xh : x∈Icc 0 (1/2:ℝ) := by
    refine ⟨xnn,(div_le_iff₀ nr).mpr ?_⟩
    have cut : 2*(h:ℝ)≤n := by exact_mod_cast (by omega : 2*h≤n)
    linarith
  have euler:=rama.euler x xh
  have posX : x.toNNReal=fraccionHuecos n h := by
    apply NNReal.eq; simp [Real.coe_toNNReal _ xnn,fraccionHuecos,x]
  have mass:=integral_masa_cuadrada euler
  rw [euler.masa,Real.coe_toNNReal _ xnn] at mass
  have lev : 1-x=(↑(n-h):ℝ)/n := by
    rw [Nat.cast_sub (by omega : h≤n)]
    dsimp [x]; field_simp
  rw [lev] at mass
  have lines:=pt x xh
  rw [posX] at lines
  intro i j
  apply balance_desde_euler_continua np (rama.espacio x xh) rama.kp (zero_le_one.trans rama.m1)
    rama.lp euler.coef mass lines _ i j
  intro f t ht
  have nn:=mul_nonneg euler.coef.le (integral_fisica_no_negativa (p x) f t ht)
  linarith only [lines f t ht,nn]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.balance_de_la_rama_puntual
