import ContinuidadDeLasCuatroFibras
open Set Filter MeasureTheory
open scoped Interval NNReal ENNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

private theorem comparar_por_conjuntos (μ : Measure ℝ) {f g : ℝ→ℝ}
    (fi : Integrable f μ) (gi : Integrable g μ)
    (eq : ∀ s : Set ℝ,MeasurableSet s → (∫ x in s,f x ∂μ)=∫ x in s,g x ∂μ) :
    f≤ᵐ[μ] g := by
  let F:=fi.aemeasurable.mk f
  let G:=gi.aemeasurable.mk g
  let s:={x | G x<F x}
  have ms : MeasurableSet s := measurableSet_lt gi.aemeasurable.measurable_mk fi.aemeasurable.measurable_mk
  have ef : f=ᵐ[μ] F := fi.aemeasurable.ae_eq_mk
  have eg : g=ᵐ[μ] G := gi.aemeasurable.ae_eq_mk
  have pos : 0≤ᵐ[μ.restrict s] (fun x => f x-g x) := by
    filter_upwards [ae_restrict_of_ae ef,ae_restrict_of_ae eg,ae_restrict_mem ms] with x ex ey hin
    change G x<F x at hin
    exact sub_nonneg.mpr (by simpa only [ex,ey] using hin.le)
  have iz : (∫ x in s,f x-g x ∂μ)=0 := by rw [integral_sub fi.integrableOn gi.integrableOn,eq s ms,sub_self]
  have z := (integral_eq_zero_iff_of_nonneg_ae pos (fi.integrableOn.sub gi.integrableOn)).mp iz
  have z' := (ae_restrict_iff' ms).mp z
  filter_upwards [ef,eg,z'] with x ex ey zz
  by_contra! h
  have hx : x∈s := by change G x<F x; simpa only [←ex,←ey] using h
  have val : f x-g x=0 := zz hx
  linarith

private theorem densidad_de_fila {f : ℝ×ℝ→ℝ} {g : ℝ→ℝ} (fi : Integrable f cuadrado) (gi : Integrable g unidad)
    (test : ∀ s : Set ℝ,MeasurableSet s →
      (∫ z,(if z.1∈s then f z else 0) ∂cuadrado)=∫ t in s,g t ∂unidad) :
    (fun x => ∫ y,f (x,y) ∂unidad)=ᵐ[unidad] g := by
  letI : IsFiniteMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  change Integrable f (unidad.prod unidad) at fi
  have equal : ∀ s : Set ℝ,MeasurableSet s → (∫ x in s,(∫ y,f (x,y) ∂unidad) ∂unidad)=∫ x in s,g x ∂unidad := by
    intro s hs
    rw [←test s hs,←integral_indicator hs]
    have ind:=fi.indicator (measurable_fst hs)
    change Integrable (fun z : ℝ×ℝ => if z.1∈s then f z else 0) (unidad.prod unidad) at ind
    rw [cuadrado,integral_prod _ ind]
    apply integral_congr_ae
    apply Eventually.of_forall; intro t
    by_cases mem : t∈s <;> simp [mem,Set.indicator]
  exact (comparar_por_conjuntos unidad fi.integral_prod_left gi equal).antisymm
    (comparar_por_conjuntos unidad gi fi.integral_prod_left (fun s hs => (equal s hs).symm))

private theorem integral_en_unidad (v : ℝ→ℝ) :
    (∫ t,v t ∂unidad)=∫ t in (0:ℝ)..1,v t := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

/-- The two rectilinear marginal densities are the row and column slice
integrals. Only the pushforward identity and the a.e. physical density are used. -/
theorem integral_euler_en_rectas {P p x b κ M L} (e : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (lp : 0≤L) (i : Fin 4) (rc : i.val<2) :
    ∀ t∈rangoF i,b*integralFisica p i t=1-holguraLinea p x i t := by
  letI : IsFiniteMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  let F:=fun z : ℝ×ℝ => b*pesoContinuo p z.1 z.2
  let f:=fun z : ℝ×ℝ => if i=0 then F z else F z.swap
  have eqF : (fun z => (P.ν z:ℝ))=ᵐ[cuadrado] F := e.real
  have intF : Integrable F cuadrado := P.masaFinita.congr eqF
  have which : i=0 ∨ i=1 := by omega
  have ref : marginalRef i=unidad := by
    rcases which with rfl|rfl <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have fi : Integrable f cuadrado := by
    rcases which with rfl|rfl
    · exact intF
    · exact (show Integrable F (unidad.prod unidad) from intF).swap
  have gi:=P.m_integrable i
  rw [ref] at gi
  have test (s : Set ℝ) (hs : MeasurableSet s) :
      (∫ z,(if z.1∈s then f z else 0) ∂cuadrado)=∫ t in s,(P.m i t:ℝ) ∂unidad := by
    let G:=fun t : ℝ => if t∈s then (1:ℝ) else 0
    have adj:=adjuncion P.ley i G (Measurable.ite hs measurable_const measurable_const)
    rw [ref] at adj
    have lhs : (∫ z,(P.ν z:ℝ)*G (coord i z) ∂cuadrado) =
        ∫ z,(if coord i z∈s then F z else 0) ∂cuadrado := by
      apply integral_congr_ae; filter_upwards [eqF] with z eq
      by_cases hz : coord i z∈s <;> simp [G,hz,eq]
    rw [lhs] at adj
    have rhs : (∫ t,(P.m i t:ℝ)*G t ∂unidad)=∫ t in s,(P.m i t:ℝ) ∂unidad := by
      rw [←integral_indicator hs]; apply integral_congr_ae; apply Eventually.of_forall; intro t
      by_cases ht : t∈s <;> simp [G,ht,Set.indicator]
    rw [rhs] at adj
    rcases which with rfl|rfl
    · simpa [f,coord] using adj
    · have swap:=integral_prod_swap (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ => if z.2∈s then F z else 0)
      exact swap.trans adj
  have canon := densidad_de_fila fi gi test
  apply euler_puntual_de_fibras_ae sp lp x i
  have vac:=e.linea i
  rw [ref] at vac ⊢
  filter_upwards [canon,vac] with t marg vac
  have val : (∫ y,f (t,y) ∂unidad)=b*integralFisica p i t := by
    rw [integral_en_unidad]
    rcases which with rfl|rfl <;> exact intervalIntegral.integral_const_mul _ _
  rw [val] at marg
  unfold TableroMedido.u at vac
  linarith

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_euler_en_rectas
