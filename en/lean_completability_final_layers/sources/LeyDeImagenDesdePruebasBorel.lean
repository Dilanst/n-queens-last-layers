import AdjuncionDelProductoDeCuatroVacancias
import RepresentantesDeLaCajaDual
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped ENNReal
theorem ley_marginal_desde_pruebas_borel {ν : ℝ×ℝ→ℝ≥0} {m : Fin 4→ℝ→ℝ≥0}
    (nm : Measurable ν) (mm : ∀ i,Measurable (m i)) (ni : Integrable (fun z=>(ν z:ℝ)) cuadrado)
    (mi : ∀ i,Integrable (fun s=>(m i s:ℝ)) (marginalRef i))
    (adj : ∀ i,∀ w : ℝ→ℝ,Measurable w → (∀ s,‖w s‖≤1) →
      (∫ z,(ν z:ℝ)*w (coord i z) ∂cuadrado)=∫ s,(m i s:ℝ)*w s ∂marginalRef i) :
    LeyMarginal ν m := by
  classical
  refine ⟨nm,mm,?_⟩
  intro i
  ext E em
  have pre := (coord_medible i) em
  rw [Measure.map_apply (coord_medible i) em,withDensity_apply _ pre,withDensity_apply _ em,
    lintegral_coe_eq_integral _ ni.integrableOn,lintegral_coe_eq_integral _ (mi i).integrableOn]
  apply congrArg ENNReal.ofReal
  let w (s : ℝ):=if s∈E then (1:ℝ) else 0
  have eq:=adj i w (Measurable.ite em measurable_const measurable_const) (fun s=>by dsimp [w]; split <;> norm_num)
  rw [←integral_indicator pre,←integral_indicator em]
  have left (z : ℝ×ℝ) : ((coord i ⁻¹' E).indicator (fun z=>(ν z:ℝ))) z=ν z*w (coord i z) := by
    by_cases h : coord i z∈E <;> simp [Set.indicator,w,h]
  have right (s : ℝ) : (E.indicator (fun s=>(m i s:ℝ))) s=m i s*w s := by
    by_cases h : s∈E <;> simp [Set.indicator,w,h]
  simpa only [left,right] using eq

def productoCuatroFisico (f : Fin 4→ℝ→ℝ) (z : ℝ×ℝ):=
  f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z)

theorem producto_cuatro_medible {f : Fin 4→ℝ→ℝ} (fm : ∀ i,Measurable (f i)) : Measurable (productoCuatroFisico f) :=
  ((((fm 0).comp (coord_medible 0)).mul ((fm 1).comp (coord_medible 1))).mul
    ((fm 2).comp (coord_medible 2))).mul ((fm 3).comp (coord_medible 3))

theorem producto_cuatro_en_unidad {f : Fin 4→ℝ→ℝ} (fb : ∀ i s,f i s∈Icc 0 1) (z : ℝ×ℝ) :
    productoCuatroFisico f z∈Icc 0 1 := by
  let v j:=f j (coord j z)
  have join {a b : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1) : a*b∈Icc 0 1 :=
    ⟨mul_nonneg ha.1 hb.1,mul_le_one₀ ha.2 hb.1 hb.2⟩
  exact join (join (join (fb 0 _) (fb 1 _)) (fb 2 _)) (fb 3 _)

theorem adjuncion_del_producto_crudo {f : Fin 4→ℝ→ℝ} (fb : ∀ i s,f i s∈Icc 0 1)
    (fm : ∀ i,Measurable (f i)) (i : Fin 4) {w : ℝ→ℝ} (wm : Measurable w) (wb : ∀ s,‖w s‖≤1) :
    (∫ z,productoCuatroFisico f z*w (coord i z) ∂cuadrado)=∫ s,f i s*cavidadFisica f i s*w s ∂marginalRef i := by
  have nn i s:=(fb i s).1
  have test:=adjuncion_del_producto_borel nn (fun i s=>(abs_of_nonneg (nn i s)).le.trans (fb i s).2) fm i w wm wb
  have form z : pesoContinuo (deCamposMedibles f) z.1 z.2=productoCuatroFisico f z := by
    change camposFisicos (deCamposMedibles f) 0 _*camposFisicos _ 1 _*camposFisicos _ 2 _*camposFisicos _ 3 _=_
    rw [campo_de_campos_medibles nn]; rfl
  simpa only [form] using test
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ley_marginal_desde_pruebas_borel
#print axioms ArticuloA.Historias.producto_cuatro_medible
#print axioms ArticuloA.Historias.producto_cuatro_en_unidad
#print axioms ArticuloA.Historias.adjuncion_del_producto_crudo
