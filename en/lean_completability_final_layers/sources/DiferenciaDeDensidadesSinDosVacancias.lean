import CamposMediblesDeLaRama
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
def densidadSeparada (p : FactoresContinuos) (b : ℝ) (z : ℝ×ℝ) :=
  b*campoR15 p 0 z.1*campoR15 p 1 z.2

theorem quitar_dos_vacancias {n m v w d a d' a' κ : ℝ} (kp : 0<κ) (mn : 0≤m)
    (hd : κ≤d) (ha : κ≤a) (hd' : κ≤d') (ha' : κ≤a') (en : n=v*d*a) (em : m=w*d'*a') :
    |v-w|≤(1/κ^2)*|n-m|+(1/κ^3)*(m*|d-d'|+m*|a-a'|) := by
  have dp:=kp.trans_le hd
  have ap:=kp.trans_le ha
  have dp':=kp.trans_le hd'
  have ap':=kp.trans_le ha'
  have eq : v-w=(n-m)/(d*a)+m*(d'-d)/(d*a*d')+m*(a'-a)/(d'*a*a') := by
    rw [en,em]; field_simp; ring
  have k2 : κ^2≤d*a := by rw [pow_two]; exact mul_le_mul hd ha kp.le dp.le
  have k3 : κ^3≤d*a*d' := by rw [pow_succ]; exact mul_le_mul k2 hd' kp.le (mul_nonneg dp.le ap.le)
  have k3' : κ^3≤d'*a*a' := by
    rw [pow_succ,pow_two]
    exact mul_le_mul (mul_le_mul hd' ha kp.le dp'.le) ha' kp.le (mul_nonneg dp'.le ap.le)
  rw [eq]
  apply ((abs_add_le ..).trans (add_le_add_right (abs_add_le ..) _)).trans
  rw [abs_div,abs_div,abs_div,abs_mul m,abs_mul m,abs_of_nonneg mn,
    abs_of_pos (mul_pos dp ap),abs_of_pos (mul_pos (mul_pos dp ap) dp'),
    abs_of_pos (mul_pos (mul_pos dp' ap) ap'),abs_sub_comm d' d,abs_sub_comm a' a]
  apply (add_le_add (add_le_add
    (div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos kp 2) k2)
    (div_le_div_of_nonneg_left (mul_nonneg mn (abs_nonneg _)) (pow_pos kp 3) k3))
    (div_le_div_of_nonneg_left (mul_nonneg mn (abs_nonneg _)) (pow_pos kp 3) k3')).trans_eq
  ring

theorem separada_integrable {p κ M L} (b : ℝ) (sp : ControlEspacial p κ M L) (lp : 0≤L) :
    Integrable (densidadSeparada p b) cuadrado := by
  letI : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance
  have co : Continuous (densidadSeparada p b) := (continuous_const.mul
    ((continuo_de_campo sp lp 0).comp continuous_fst)).mul ((continuo_de_campo sp lp 1).comp continuous_snd)
  apply integrable_acotada_probabilidad co.measurable (C:=|b| *M*M)
  intro z
  unfold densidadSeparada
  rw [abs_mul,abs_mul,abs_of_nonneg (a:=campoR15 p 0 z.1) (NNReal.coe_nonneg _),
    abs_of_nonneg (a:=campoR15 p 1 z.2) (NNReal.coe_nonneg _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (banda_de_campo sp 0 z.1).2 (abs_nonneg _))
    (banda_de_campo sp 1 z.2).2 (NNReal.coe_nonneg _)
    (mul_nonneg (abs_nonneg _) ((NNReal.coe_nonneg _ : 0≤campoR15 p 0 z.1).trans (banda_de_campo sp 0 z.1).2))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.quitar_dos_vacancias
#print axioms ArticuloA.Historias.separada_integrable
