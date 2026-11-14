import AdjuncionDeFibrasParaPruebasBorel
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
def deCamposMedibles (f : Fin 4→ℝ→ℝ) : FactoresContinuos :=
  ⟨fun s=>(f 0 s).toNNReal,fun s=>(f 1 s).toNNReal,fun s=>(f 2 s).toNNReal,fun s=>(f 3 s).toNNReal⟩

theorem campo_de_campos_medibles {f : Fin 4→ℝ→ℝ} (nn : ∀ i s,0≤f i s) :
    camposFisicos (deCamposMedibles f)=f := by
  funext i s
  fin_cases i <;> exact Real.coe_toNNReal _ (nn _ s)

theorem adjuncion_del_producto_borel {f : Fin 4→ℝ→ℝ} (nn : ∀ i s,0≤f i s)
    (cap : ∀ i s,|f i s|≤1) (fm : ∀ i,Measurable (f i)) (i : Fin 4)
    (w : ℝ→ℝ) (wm : Measurable w) (wb : ∀ s,‖w s‖≤1) :
    let p:=deCamposMedibles f
    (∫ z,pesoContinuo p z.1 z.2*w (coord i z) ∂cuadrado)=
      ∫ s,f i s*cavidadFisica f i s*w s ∂marginalRef i := by
  let p:=deCamposMedibles f
  let U (z : ℝ×ℝ):=pesoContinuo p z.1 z.2
  have form z : U z=f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z) := by
    change camposFisicos p 0 _*camposFisicos p 1 _*camposFisicos p 2 _*camposFisicos p 3 _=_
    rw [campo_de_campos_medibles nn]; rfl
  have um : Measurable U := by
    simp_rw [show U=(fun z=>f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z)) from funext form]
    exact ((((fm 0).comp (coord_medible 0)).mul ((fm 1).comp (coord_medible 1))).mul
      ((fm 2).comp (coord_medible 2))).mul ((fm 3).comp (coord_medible 3))
  have ub z : ‖U z‖≤1 := by
    rw [form,norm_mul,norm_mul,norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (mul_le_one₀ (cap _ _) (norm_nonneg _) (cap _ _)) (norm_nonneg _) (cap _ _))
      (norm_nonneg _) (cap _ _)
  have fiber j s : integralFisica p j s=f j s*cavidadFisica f j s := by
    rw [factor_de_la_familia_por_su_cavidad,campo_de_campos_medibles nn]
  have ob (a : Bool) : (∫ z,U z*w (coord (indiceDeLaSeccion a) z) ∂cuadrado)=
      ∫ s,f (indiceDeLaSeccion a) s*cavidadFisica f (indiceDeLaSeccion a) s*w s ∂marginalRef (indiceDeLaSeccion a) := by
    rw [adjuncion_de_diagonal_borel U w um wm ub wb a]
    have ref : marginalRef (indiceDeLaSeccion a)=(if a then anti else diag) := by
      cases a <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
    rw [←ref]; apply integral_congr_ae; filter_upwards [linea_en_dominio (indiceDeLaSeccion a)] with s hs
    cases a
    · exact congrArg (·*w s) ((carga_en_la_etiqueta_fisica p 1 hs).trans (fiber 2 s))
    · exact congrArg (·*w s) ((carga_en_la_etiqueta_fisica p 2 hs).trans (fiber 3 s))
  fin_cases i
  · change (∫ z,U z*w z.1 ∂cuadrado)=_
    rw [adjuncion_de_fila_borel U w um wm ub wb,←show marginalRef 0=unidad from Measure.restrict_congr_set Ioc_ae_eq_Icc]
    apply integral_congr_ae; exact Eventually.of_forall (fun s=>congrArg (·*w s) (fiber 0 s))
  · have rev:=integral_prod_swap (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ=>U z*w z.2)
    change (∫ z,U z.swap*w z.1 ∂cuadrado)=(∫ z,U z*w z.2 ∂cuadrado) at rev
    change (∫ z,U z*w z.2 ∂cuadrado)=_
    rw [←rev,adjuncion_de_fila_borel (fun z=>U z.swap) w (um.comp measurable_swap) wm (fun z=>ub z.swap) wb,
      ←show marginalRef 1=unidad from Measure.restrict_congr_set Ioc_ae_eq_Icc]
    apply integral_congr_ae; exact Eventually.of_forall (fun s=>congrArg (·*w s) (fiber 1 s))
  · exact ob false
  · exact ob true
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.campo_de_campos_medibles
#print axioms ArticuloA.Historias.adjuncion_del_producto_borel
