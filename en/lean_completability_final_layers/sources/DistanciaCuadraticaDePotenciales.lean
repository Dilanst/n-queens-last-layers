import CajaCompletaDeLosCuatroPotenciales
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem norma_L2_cuadrada {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℝ 2 μ) :
    ‖u‖^2=∫ s,(u s)^2 ∂μ := by
  have id:=(Lp.memLp u).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [Lp.norm_def,id]
  have nn : 0≤∫ s,u s^2 ∂μ := integral_nonneg (fun _=>sq_nonneg _)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [ENNReal.toReal_ofReal (rpow_nonneg nn _)]
  exact rpow_inv_natCast_pow (n:=2) nn (by decide)

theorem distancia_L2_por_representantes {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u v : Lp ℝ 2 μ) {f g : α→ℝ} (fu : f=ᵐ[μ] u) (gv : g=ᵐ[μ] v) :
    (dist u v)^2=∫ s,(f s-g s)^2 ∂μ := by
  rw [dist_eq_norm,norma_L2_cuadrada]
  apply integral_congr_ae; filter_upwards [fu,gv,Lp.coeFn_sub u v] with s hs ht eq
  rw [hs,ht,eq]; rfl

theorem abs_exp_neg_lipschitz {u v : ℝ} (un : 0≤u) (vn : 0≤v) : |exp (-u)-exp (-v)|≤|u-v| := by
  have forward {y z : ℝ} (yn : 0≤y) (yz : y≤z) : exp (-y)-exp (-z)≤z-y := by
    have help:=mul_le_mul_of_nonneg_left (add_one_le_exp (y-z)) (exp_pos (-y)).le
    rw [←exp_add,show -y+(y-z)= -z by ring] at help
    have cap:=mul_le_of_le_one_right (sub_nonneg.mpr yz) (exp_le_one_iff.mpr (neg_nonpos.mpr yn))
    nlinarith only [help,cap]
  rcases le_total u v with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (neg_le_neg h))),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith only [forward un h]
  · rw [abs_of_nonpos (sub_nonpos.mpr (exp_le_exp.mpr (neg_le_neg h))),abs_of_nonneg (sub_nonneg.mpr h)]
    linarith only [forward vn h]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.norma_L2_cuadrada
#print axioms ArticuloA.Historias.distancia_L2_por_representantes
#print axioms ArticuloA.Historias.abs_exp_neg_lipschitz
