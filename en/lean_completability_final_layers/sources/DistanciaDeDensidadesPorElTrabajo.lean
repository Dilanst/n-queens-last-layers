import TrabajoConjuntoDeDosTableros
import DiferenciaDelProductoDeTresFactores
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Filter Perfil
local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance

private theorem secante_inversa {a b U : ℝ} (ap : 0<a) (bp : 0<b) (au : a≤U) (bu : b≤U) :
    (a-b)^2≤U*((a-b)*(Real.log a-Real.log b)) := by
  have s:=diferencia_exponencial_desde_arriba (a:=Real.log a) (b:=Real.log b) (K:=U)
    (by rwa [Real.exp_log ap]) (by rwa [Real.exp_log bp])
  rw [Real.exp_log ap,Real.exp_log bp] at s
  rcases le_total a b with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ap h))] at s
    nlinarith only [mul_le_mul_of_nonneg_left s (sub_nonneg.mpr h)]
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log bp h))] at s
    nlinarith only [mul_le_mul_of_nonneg_left s (sub_nonneg.mpr h)]

theorem densidad_en_banda {P p x b κ M L} (e : EulerFisica P p x b) (s : ControlEspacial p κ M L) (hk : 0<κ) :
    ∀ᵐ z ∂cuadrado, b*κ^4≤(P.ν z:ℝ) ∧ (P.ν z:ℝ)≤b*M^4 := by
  filter_upwards [densidad_en_factores_recortados e] with z eq
  rw [eq]
  have fac (i : Fin 4) := banda_de_campo s i (coord i z)
  have pos (i : Fin 4) : 0≤campoR15 p i (coord i z) := hk.le.trans (fac i).1
  change _≤b*campoR15 p 0 (coord 0 z)*campoR15 p 1 (coord 1 z)*campoR15 p 2 (coord 2 z)*campoR15 p 3 (coord 3 z) ∧ _≤_
  have src (k : ℝ) : b*k^4=b*k*k*k*k := by ring
  rw [src κ,src M]
  have four (a r c d t R C D T : ℝ) (ba : 0≤a) (rr : 0≤r) (cc : 0≤c) (dd : 0≤d) (tt : 0≤t)
      (hr : r≤R) (hc : c≤C) (hd : d≤D) (ht : t≤T) : a*r*c*d*t≤a*R*C*D*T := by
    have h1:=mul_le_mul_of_nonneg_left hr ba
    have n1:=mul_nonneg ba (rr.trans hr)
    have n2:=mul_nonneg n1 (cc.trans hc)
    have n3:=mul_nonneg n2 (dd.trans hd)
    exact mul_le_mul (mul_le_mul (mul_le_mul h1 hc cc n1) hd dd n2) ht tt n3
  exact ⟨four _ _ _ _ _ _ _ _ _ e.coef.le hk.le hk.le hk.le hk.le (fac 0).1 (fac 1).1 (fac 2).1 (fac 3).1,
    four _ _ _ _ _ _ _ _ _ e.coef.le (pos 0) (pos 1) (pos 2) (pos 3) (fac 0).2 (fac 1).2 (fac 2).2 (fac 3).2⟩

theorem distancia_cuadrada_acotada (P Q : TableroMedido) {m U : ℝ} (mp : 0<m)
    (pband : ∀ᵐ z ∂cuadrado,m≤(P.ν z:ℝ) ∧ (P.ν z:ℝ)≤U)
    (qband : ∀ᵐ z ∂cuadrado,m≤(Q.ν z:ℝ) ∧ (Q.ν z:ℝ)≤U) :
    (distanciaTableros P Q)^2≤U*trabajoRelativo P Q := by
  let d:=fun z=>((P.ν z:ℝ)-Q.ν z)
  let v:=fun z=>Real.log (P.ν z)-Real.log (Q.ν z)
  let dabs:=fun z=>|d z|
  let A:=distanciaTableros P Q
  have idn : Integrable d cuadrado := P.masaFinita.sub Q.masaFinita
  have iabs : Integrable dabs cuadrado := idn.abs
  have md : Measurable d := P.ley.densidad.coe_nnreal_real.sub Q.ley.densidad.coe_nnreal_real
  have mv : Measurable v := P.ley.densidad.coe_nnreal_real.log.sub Q.ley.densidad.coe_nnreal_real.log
  have i2 : Integrable (fun z=>d z^2) cuadrado := by
    apply (integrable_const (U^2)).mono' (md.pow_const 2).aestronglyMeasurable
    filter_upwards [pband,qband] with z h g
    change |d z^2|≤U^2
    rw [abs_of_nonneg (sq_nonneg (d z))]
    apply sq_le_sq'
    · change -U≤(P.ν z:ℝ)-Q.ν z; linarith [h.1,g.2]
    · change (P.ν z:ℝ)-Q.ν z≤U; linarith [g.1,h.2]
  have iw : Integrable (fun z=>d z*v z) cuadrado := by
    apply (integrable_const (U*(2*(|Real.log m|+|Real.log U|)))).mono' (md.mul mv).aestronglyMeasurable
    filter_upwards [pband,qband] with z h g
    have logs {w : ℝ} (lo : m≤w) (hi : w≤U) : |Real.log w|≤|Real.log m|+|Real.log U| :=
      abs_le.mpr ⟨by linarith [Real.log_le_log mp lo,neg_abs_le (Real.log m),abs_nonneg (Real.log U)],
        by linarith [Real.log_le_log (mp.trans_le lo) hi,le_abs_self (Real.log U),abs_nonneg (Real.log m)]⟩
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (abs_le.mpr ⟨by dsimp [d]; linarith [h.1,g.2],by dsimp [d]; linarith [g.1,h.2]⟩)
      ((abs_sub _ _).trans (by linarith only [logs h.1 h.2,logs g.1 g.2])) (abs_nonneg _) (mp.le.trans (h.1.trans h.2))
  have a2 : A^2≤∫ z,d z^2 ∂cuadrado := by
    have mono:=integral_mono (iabs.const_mul (2*A)) (i2.add (integrable_const (A^2)))
      (fun z=>show 2*A*dabs z≤d z^2+A^2 by nlinarith only [sq_nonneg (|d z|-A),sq_abs (d z)])
    simp only [Pi.add_apply] at mono
    rw [integral_const_mul,integral_add i2 (integrable_const _),integral_const] at mono
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at mono
    change 2*A*A≤_ at mono
    linarith only [mono]
  have fin:=integral_mono_ae i2 (iw.const_mul U) ((pband.and qband).mono
    (fun z h=>secante_inversa (mp.trans_le h.1.1) (mp.trans_le h.2.1) h.1.2 h.2.2))
  rw [integral_const_mul] at fin
  exact a2.trans fin
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.densidad_en_banda
#print axioms ArticuloA.Historias.distancia_cuadrada_acotada
