import ContinuidadDeLasCuatroCavidadesMedibles
import AdjuncionDelProductoDeCuatroVacancias
import ConjuntosNulosDeLasCuatroEtiquetas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Classical
theorem ecuacion_de_fibra_del_optimo_medible {P : TableroMedido} {a : ℝ} {f : Fin 4→ℝ→ℝ}
    (fi : ∀ i,Integrable (f i)) (fm : ∀ i,Measurable (f i)) (nn : ∀ i y,0≤f i y)
    (cap : ∀ i y,|f i y|≤1)
    (area : ∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=a*f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z))
    (line : ∀ i,∀ᵐ s ∂marginalRef i,P.u i s=f i s) (i : Fin 4) :
    ∀ᵐ s ∂marginalRef i,f i s*(1+a*cavidadFisica f i s)=1 := by
  let C s:=cavidadFisica f i (recorte i s)
  let g s:=a*(f i s*C s)
  let m s:=(P.m i s:ℝ)
  have cf:=cavidad_continua_para_campos_medibles f fi fm 1 cap i
  have cc : Continuous C := cf.comp_continuous
    (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)
  have cg : Measurable g := measurable_const.mul ((fm i).mul cc.measurable)
  have cm : Measurable m := (P.ley.densidadLinea i).coe_nnreal_real
  have cb s : ‖C s‖≤1 := by
    have l:=longitud_en_unidad i (recorte_dentro i s)
    have bd (t : ℝ) : ‖productoEnCuerda f i (recorte i s) t‖≤1 := by
      dsimp only [productoEnCuerda]
      rw [norm_mul,norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (cap _ _) (norm_nonneg _) (cap _ _)) (norm_nonneg _) (cap _ _)
    have val:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=longitudDeCuerda i (recorte i s))
      (fun t _=>bd t)
    simpa only [sub_zero,abs_of_nonneg l.1,one_mul] using val.trans (by simpa [abs_of_nonneg l.1] using l.2)
  have gb s : ‖g s‖≤|a| := by
    dsimp only [g]; rw [norm_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_left (mul_le_one₀ (cap _ _) (norm_nonneg _) (cb s)) (norm_nonneg a)).trans_eq (mul_one _)
  have gi : Integrable g (marginalRef i) :=
    (integrable_const |a|).mono' cg.aestronglyMeasurable (Eventually.of_forall gb)
  let w s:ℝ:=if g s≤m s then 1 else -1
  have wm : Measurable w := Measurable.ite (measurableSet_le cg cm) measurable_const measurable_const
  have wb s : ‖w s‖≤1 := by dsimp only [w]; split <;> norm_num
  have gmW : Integrable (fun s=>g s*w s) (marginalRef i) := by
    apply (integrable_const |a|).mono' ((cg.mul wm).aestronglyMeasurable)
    filter_upwards with s; rw [norm_mul]
    exact (mul_le_mul (gb s) (wb s) (norm_nonneg _) (abs_nonneg _)).trans_eq (mul_one _)
  have mmW : Integrable (fun s=>m s*w s) (marginalRef i) := by
    apply (P.m_integrable i).mono ((cm.mul wm).aestronglyMeasurable)
    filter_upwards with s; rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (wb s) (norm_nonneg _)).trans_eq (mul_one _)
  have raw z : pesoContinuo (deCamposMedibles f) z.1 z.2 =
      f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z) := by
    change camposFisicos (deCamposMedibles f) 0 _*camposFisicos _ 1 _*camposFisicos _ 2 _*camposFisicos _ 3 _=_
    rw [campo_de_campos_medibles nn]; rfl
  have test : (∫ s,m s*w s ∂marginalRef i)=∫ s,g s*w s ∂marginalRef i := by
    rw [←adjuncion P.ley i w wm]
    calc
      _ = ∫ z,a*(pesoContinuo (deCamposMedibles f) z.1 z.2*w (coord i z)) ∂cuadrado := by
        apply integral_congr_ae; filter_upwards [area] with z hz; rw [hz,raw]; ring
      _ = a*∫ s,f i s*cavidadFisica f i s*w s ∂marginalRef i := by
        rw [integral_const_mul,adjuncion_del_producto_borel nn cap fm i w wm wb]
      _ = _ := by
        rw [←integral_const_mul]; apply integral_congr_ae
        filter_upwards [linea_en_dominio i] with s hs
        dsimp only [g,C]; rw [recorte_fijo i hs]; ring
  have ae : (fun s=>m s*w s-g s*w s)=ᵐ[marginalRef i] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae _ (mmW.sub gmW)).mp
    · change (∫ s,m s*w s-g s*w s ∂marginalRef i)=0
      rw [integral_sub mmW gmW,test,sub_self]
    · apply Eventually.of_forall; intro s; change 0≤m s*w s-g s*w s
      by_cases h : g s≤m s
      · simpa only [w,if_pos h,mul_one] using sub_nonneg.mpr h
      · simp only [w,if_neg h,mul_neg,mul_one]; linarith
  filter_upwards [ae,line i,linea_en_dominio i] with s hz hl hs
  change m s*w s-g s*w s=0 at hz
  have eq : m s=g s := by dsimp only [w] at hz; split at hz <;> linarith
  change 1-m s=f i s at hl
  dsimp only [g,C] at eq; rw [recorte_fijo i hs] at eq
  nlinarith only [eq,hl]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ecuacion_de_fibra_del_optimo_medible
