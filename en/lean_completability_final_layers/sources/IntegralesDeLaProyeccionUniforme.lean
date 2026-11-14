import AdjuncionDelProductoDeCuatroVacancias
import CajaCompletaDeLosCuatroPotenciales
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem integral_en_la_etiqueta_uniforme (i : Fin 4) {w : ℝ→ℝ}
    (wm : Measurable w) (bd : ∀ s,‖w s‖≤1) :
    (∫ z,w (coord i z) ∂cuadrado)=∫ s,longitudDeCuerda i s*w s ∂marginalRef i := by
  let f : Fin 4→ℝ→ℝ:=fun _ _=>1
  have cv s : cavidadFisica f i s=longitudDeCuerda i s := by
    simp [cavidadFisica,productoEnCuerda,restriccionACuerda,f]
  have t:=adjuncion_del_producto_borel (f:=f) (fun _ _=>zero_le_one) (fun _ _=>by norm_num [f])
    (fun _=>measurable_const) i w wm bd
  simpa only [cv,f,pesoContinuo,deCamposMedibles,Real.toNNReal_one,NNReal.coe_one,one_mul] using t

theorem integral_del_levantamiento_acotado (i : Fin 4) {w : ℝ→ℝ} (wm : Measurable w)
    {M : ℝ} (bd : ∀ s,|w s|≤M) (nn : ∀ s,0≤w s) :
    (∫ z,w (coord i z) ∂cuadrado)≤∫ s,w s ∂marginalRef i := by
  let D:=max M 1
  have dp : 0<D := zero_lt_one.trans_le (le_max_right _ _)
  let v s:=w s/D
  have vb s : ‖v s‖≤1 := by
    change |w s/D|≤1; rw [abs_div,abs_of_pos dp]
    exact (div_le_one dp).mpr ((bd s).trans (le_max_left _ _))
  have eq:=integral_en_la_etiqueta_uniforme i (wm.div_const D) vb
  have vi : Integrable v (marginalRef i) := (integrable_const (1:ℝ)).mono' (wm.div_const D).aestronglyMeasurable
    (Eventually.of_forall vb)
  have meas : Measurable (longitudDeCuerda i) := by unfold longitudDeCuerda; fin_cases i <;> simp [desplazamientoOblicuo] <;> fun_prop
  have li : Integrable (fun s=>longitudDeCuerda i s*v s) (marginalRef i) := by
    apply vi.mono ((meas.mul (wm.div_const D)).aestronglyMeasurable)
    filter_upwards [linea_en_dominio i] with s hs
    rw [norm_mul,Real.norm_eq_abs (longitudDeCuerda i s),abs_of_nonneg (longitud_en_unidad i hs).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (longitud_en_unidad i hs).2
  have comp:=integral_mono_ae li vi (by
    filter_upwards [linea_en_dominio i] with s hs
    exact mul_le_of_le_one_left (div_nonneg (nn s) dp.le) (longitud_en_unidad i hs).2)
  have h:=eq.le.trans comp
  change (∫ z,w (coord i z)/D ∂cuadrado)≤∫ s,w s/D ∂marginalRef i at h
  rwa [integral_div,integral_div,div_le_div_iff_of_pos_right dp] at h
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_en_la_etiqueta_uniforme
#print axioms ArticuloA.Historias.integral_del_levantamiento_acotado
