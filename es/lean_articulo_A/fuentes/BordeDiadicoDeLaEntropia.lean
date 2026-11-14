import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open Filter Set
open scoped Topology
namespace ArticuloA.Perfil
noncomputable section

private def barrera (B x : ℝ) := -(2*(Real.log x*x))+B*x

theorem soporte_a_borde (S : ℝ→ℝ) (C : ℝ) (cont : ContinuousWithinAt S (Icc 0 (1/2:ℝ)) 0)
    (soporte : ∀ y : ℝ,0<y → y≤1/4 → S (2*y)-S y≤y*(C-2*Real.log y))
    (x : ℝ) (xp : 0<x) (x1 : x≤1/2) :
    S x-S 0≤ -(2*(Real.log x*x))+(C+4*Real.log 2)*x := by
  let B := C+4*Real.log 2
  let w (j : ℕ) := x*(1/2:ℝ)^j
  have wp (j : ℕ) : 0<w j := by dsimp [w]; positivity
  have wb (j : ℕ) : w j≤1/2 :=
    (mul_le_of_le_one_right xp.le (pow_le_one₀ (by norm_num : 0≤(1/2:ℝ)) (by norm_num))).trans x1
  have halve (j : ℕ) : w (j+1)=w j/2 := by simp only [w,pow_succ]; ring
  have step (j : ℕ) : S (w j)-barrera B (w j)≤S (w (j+1))-barrera B (w (j+1)) := by
    rw [halve]
    have e:=soporte (w j/2) (by positivity) (by linarith [wb j])
    rw [show 2*(w j/2)=w j by ring,Real.log_div (wp j).ne' (by norm_num)] at e
    simp only [barrera,B,Real.log_div (wp j).ne' (by norm_num : (2:ℝ)≠0)]
    linarith only [e]
  have lower (j : ℕ) : S x-barrera B x≤S (w j)-barrera B (w j) := by
    induction j with
    | zero => simp [w]
    | succ j ih => exact ih.trans (step j)
  have zero : Tendsto w atTop (𝓝 0) := by
    simpa only [w,mul_zero] using (tendsto_const_nhds (x:=x)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num))
  have pos : Tendsto w atTop (𝓝[>] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨zero,Eventually.of_forall wp⟩
  have domain : Tendsto w atTop (𝓝[Icc 0 (1/2:ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨zero,Eventually.of_forall (fun j => ⟨(wp j).le,wb j⟩)⟩
  have lm : Tendsto (fun z : ℝ => Real.log z*z) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have vanish : Tendsto (fun j => barrera B (w j)) atTop (𝓝 0) := by
    simpa only [barrera,Function.comp_def,mul_zero,neg_zero,add_zero] using
      (((tendsto_const_nhds (x:=(2:ℝ))).mul (lm.comp pos)).neg.add ((tendsto_const_nhds (x:=B)).mul zero))
  have result := le_of_tendsto_of_tendsto' (tendsto_const_nhds (x:=S x-barrera B x))
    ((cont.tendsto.comp domain).sub vanish) lower
  simp only [sub_zero] at result
  change S x-(-(2*(Real.log x*x))+B*x)≤S 0 at result
  dsimp only [B] at result
  linarith only [result]

theorem borde_para_K_fijo (S : ℝ→ℝ) (C : ℝ) (cont : ContinuousWithinAt S (Icc 0 (1/2:ℝ)) 0)
    (soporte : ∀ y : ℝ,0<y → y≤1/4 → S (2*y)-S y≤y*(C-2*Real.log y))
    (n h K : ℕ) (hn : 0<n) (hk : h≤K) (size : 2*K≤n) :
    (n:ℝ)*(S ((h:ℝ)/n)-S 0)≤2*h*Real.log n+(K:ℝ)*max (C+4*Real.log 2) 0 := by
  let B:=C+4*Real.log 2
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  by_cases z : h=0
  · subst h; simp only [Nat.cast_zero,zero_div,sub_self,mul_zero,zero_mul,zero_add]; positivity
  have hp : 0<(h:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero z
  have h1 : 1≤(h:ℝ) := by exact_mod_cast (by omega : 1≤h)
  have le : 2*(h:ℝ)≤n := by exact_mod_cast (by omega : 2*h≤n)
  have e:=mul_le_mul_of_nonneg_left (soporte_a_borde S C cont soporte ((h:ℝ)/n) (div_pos hp np)
    ((div_le_iff₀ np).mpr (by linarith))) np.le
  have eq : (n:ℝ)*(-(2*(Real.log ((h:ℝ)/n)*((h:ℝ)/n)))+B*((h:ℝ)/n))=
      2*h*Real.log n-2*h*Real.log h+h*B := by
    rw [Real.log_div hp.ne' np.ne']; field_simp; ring
  change (n:ℝ)*(S ((h:ℝ)/n)-S 0)≤(n:ℝ)*(-(2*(Real.log ((h:ℝ)/n)*((h:ℝ)/n)))+B*((h:ℝ)/n)) at e
  rw [eq] at e
  have hb : (h:ℝ)*B≤(K:ℝ)*max B 0 :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hp.le).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (le_max_right _ _))
  have sign := mul_nonneg (show 0≤2*(h:ℝ) by positivity) (Real.log_nonneg h1)
  change (n:ℝ)*(S ((h:ℝ)/n)-S 0)≤2*h*Real.log n+(K:ℝ)*max B 0
  exact e.trans (add_le_add (sub_le_self _ sign) hb)
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.soporte_a_borde
#print axioms ArticuloA.Perfil.borde_para_K_fijo
