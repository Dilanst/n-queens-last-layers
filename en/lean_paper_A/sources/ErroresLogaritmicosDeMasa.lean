import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
open scoped BigOperators
namespace ArticuloA.Perfil
noncomputable section

theorem log_sobre_referencia (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    v*(Real.log u-Real.log v)≤u-v := by
  have a := (Real.log_le_sub_one_of_pos (div_pos hu hv))
  rw [Real.log_div hu.ne' hv.ne'] at a
  have t := mul_le_mul_of_nonneg_left a hv.le
  convert t using 1
  field_simp

theorem lipschitz_del_log {u v κ D : ℝ} (kp : 0<κ) (hu : κ≤u) (hv : κ≤v)
    (difference : |u-v|≤D) : |Real.log u-Real.log v|≤D/κ := by
  have up := kp.trans_le hu
  have vp := kp.trans_le hv
  have bound (x y : ℝ) (py : κ≤y) (px : 0<x) (dif : x-y≤D) :
      Real.log x-Real.log y≤D/κ := by
    by_cases neg : Real.log x-Real.log y≤0
    · exact neg.trans (div_nonneg ((abs_nonneg _).trans difference) kp.le)
    apply (le_div_iff₀ kp).mpr
    exact (mul_le_mul_of_nonneg_left py (le_of_lt (lt_of_not_ge neg))).trans
      ((by simpa [mul_comm] using log_sobre_referencia x y px (kp.trans_le py) : (Real.log x-Real.log y)*y≤x-y).trans dif)
  exact abs_le.mpr ⟨by have a := bound v u hu vp (by linarith [(abs_le.mp difference).1]); linarith,
    bound u v hv up (abs_le.mp difference).2⟩

theorem error_de_masa_real (n q : ℕ) (hn : 0<n) (hq : 0<q) (qn : q≤n)
    (x b m m₀ S C : ℝ) (xp : 0<x) (bp : 0<b) (mp : 0<m₀) (cn : 0≤C) (low : m₀≤m) (sp : 0<S)
    (mass : m=(q:ℝ)/(n*b)) (err : S-(n:ℝ)^2*m≤C*n) :
    (q:ℝ)*(Real.log (x^2*S)-(Real.log n+Real.log q-Real.log (b/x^2)))≤C/m₀ := by
  have npos : (0:ℝ)<n := by exact_mod_cast hn
  have qpos : (0:ℝ)<q := by exact_mod_cast hq
  have ref : (n:ℝ)^2*m=n*q/b := by rw [mass]; field_simp; ring
  have Rpos := mul_pos (sq_pos_of_pos npos) (mp.trans_le low)
  have a := log_sobre_referencia S ((n:ℝ)^2*m) sp Rpos
  have eq : Real.log (x^2*S)-(Real.log n+Real.log q-Real.log (b/x^2))=
      Real.log S-Real.log ((n:ℝ)^2*m) := by
    rw [ref,Real.log_mul (pow_ne_zero _ xp.ne') sp.ne',Real.log_div bp.ne' (pow_ne_zero _ xp.ne'),
      Real.log_div (mul_ne_zero npos.ne' qpos.ne') bp.ne',Real.log_mul npos.ne' qpos.ne']; ring
  rw [eq]
  have fin := a.trans err
  have b₁ : Real.log S-Real.log ((n:ℝ)^2*m)≤C/(n*m) := by
    apply (le_div_iff₀ (mul_pos npos (mp.trans_le low))).mpr
    apply (mul_le_mul_iff_of_pos_left npos).mp; nlinarith only [fin]
  have pre := mul_le_mul_of_nonneg_left b₁ qpos.le
  apply pre.trans
  have f : (q:ℝ)*m₀≤(n:ℝ)*m := mul_le_mul (by exact_mod_cast qn) low mp.le npos.le
  apply (le_div_iff₀ mp).mpr
  rw [←mul_div_assoc,div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos npos (mp.trans_le low))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left f cn]

theorem error_de_masa_virtual (H C : ℝ) (hp : 0<H) (U : Fin 4→ℝ) (pos : ∀ j,0<U j)
    (upper : ∀ j,U j-H≤C) :
    H*(Real.log (∏ j,U j)-4*Real.log H)≤4*C := by
  have e (j) := (log_sobre_referencia (U j) H (pos j) hp).trans (upper j)
  rw [Fin.prod_univ_four,Real.log_mul (mul_ne_zero (mul_ne_zero (pos 0).ne' (pos 1).ne') (pos 2).ne') (pos 3).ne',
    Real.log_mul (mul_ne_zero (pos 0).ne' (pos 1).ne') (pos 2).ne',Real.log_mul (pos 0).ne' (pos 1).ne']
  linarith only [e 0,e 1,e 2,e 3]
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.error_de_masa_real
#print axioms ArticuloA.Perfil.error_de_masa_virtual
