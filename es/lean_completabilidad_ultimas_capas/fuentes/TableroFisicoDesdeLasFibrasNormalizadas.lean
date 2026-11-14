import LeyDeImagenDesdePruebasBorel
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
local instance : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance

theorem tablero_desde_fibras_normalizadas {d a : ℝ} (ap : 0<a) {f : Fin 4→ℝ→ℝ}
    (fb : ∀ i s,f i s∈Icc 0 1) (fm : ∀ i,Measurable (f i))
    (mass : a*(∫ z,productoCuatroFisico f z ∂cuadrado)=d)
    (fiber : ∀ i,∀ᵐ s ∂marginalRef i,1-f i s=a*(f i s*cavidadFisica f i s)) :
    ∃ P : TableroMedido,P.rho=d ∧
    (∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=a*f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z)) ∧
    ∀ i,∀ᵐ s ∂marginalRef i,P.u i s=f i s := by
  let ν (z : ℝ×ℝ):=(a*productoCuatroFisico f z).toNNReal
  let m (i : Fin 4) (s : ℝ):=(1-f i s).toNNReal
  have V z : (ν z:ℝ)=a*productoCuatroFisico f z := Real.coe_toNNReal _ (mul_nonneg ap.le (producto_cuatro_en_unidad fb z).1)
  have M i s : (m i s:ℝ)=1-f i s := Real.coe_toNNReal _ (sub_nonneg.mpr (fb i s).2)
  have vm : Measurable ν := (measurable_const.mul (producto_cuatro_medible fm)).real_toNNReal
  have mm i : Measurable (m i) := (measurable_const.sub (fm i)).real_toNNReal
  have vi : Integrable (fun z=>(ν z:ℝ)) cuadrado := by
    apply integral_acotada_dual vm.coe_nnreal_real (M:=a)
    intro z; rw [abs_of_nonneg (ν z).coe_nonneg,V]
    exact mul_le_of_le_one_right ap.le (producto_cuatro_en_unidad fb z).2
  have mi i : Integrable (fun s=>(m i s:ℝ)) (marginalRef i) := by
    apply integral_acotada_dual (mm i).coe_nnreal_real (M:=1)
    intro s; rw [abs_of_nonneg (m i s).coe_nonneg,M]; linarith [(fb i s).1]
  have law : LeyMarginal ν m := by
    apply ley_marginal_desde_pruebas_borel vm mm vi mi
    intro i w wm wb
    simp only [V,M]
    calc
      _ = a*(∫ z,productoCuatroFisico f z*w (coord i z) ∂cuadrado) := by
        rw [←integral_const_mul]; apply integral_congr_ae; exact Eventually.of_forall (fun _=>mul_assoc _ _ _)
      _ = _ := by
        rw [adjuncion_del_producto_crudo fb fm i wm wb,←integral_const_mul]
        apply integral_congr_ae; filter_upwards [fiber i] with s hs; rw [hs]; ring
  let P : TableroMedido:=⟨ν,m,law,vi,fun i=>Eventually.of_forall (fun s=>
    (M i s).le.trans (sub_le_self 1 (fb i s).1))⟩
  refine ⟨P,?_,?_,?_⟩
  · change (∫ z,(ν z:ℝ) ∂cuadrado)=d; simp only [V,integral_const_mul,mass]
  · apply Eventually.of_forall; intro z; change (ν z:ℝ)=_; rw [V]; unfold productoCuatroFisico; ring
  · intro i; apply Eventually.of_forall; intro s
    change 1-(m i s:ℝ)=f i s; rw [M]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tablero_desde_fibras_normalizadas
