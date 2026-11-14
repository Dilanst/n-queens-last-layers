import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic.Linarith
open MeasureTheory Set
open scoped ENNReal
namespace ArticuloA.Perfil
noncomputable section

def unidad : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
def cuadrado : Measure (ℝ×ℝ) := unidad.prod unidad

private theorem masa_unidad : unidad univ=1 := by
  simp [unidad,Real.volume_Icc]

private instance : IsFiniteMeasure unidad := ⟨by rw [masa_unidad]; exact ENNReal.one_lt_top⟩

theorem levantar_fila (f : ℝ→ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z.1 ∂cuadrado = ∫⁻ x, f x ∂unidad := by
  rw [cuadrado,lintegral_prod (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ => f z.1) (hf.comp measurable_fst).aemeasurable]
  simp [lintegral_const,masa_unidad]

theorem levantar_columna (f : ℝ→ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z.2 ∂cuadrado = ∫⁻ x, f x ∂unidad := by
  rw [cuadrado,lintegral_prod_symm (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ => f z.2) (hf.comp measurable_snd).aemeasurable]
  simp [lintegral_const,masa_unidad]

private theorem trasladar_fibra (f : ℝ→ℝ≥0∞) (hf : Measurable f) (d : ℝ) (S : Set ℝ)
    (hs : MeasurableSet S) (sub : Icc (0:ℝ) 1⊆(fun r : ℝ => r+d) ⁻¹' S) :
    (∫⁻ r,f (r+d) ∂unidad)≤∫⁻ y in S,f y := by
  exact (lintegral_mono_set sub).trans_eq
    ((measurePreserving_add_right (volume:Measure ℝ) d).setLIntegral_comp_preimage hs hf)

private theorem integrar_cota {g : ℝ→ℝ≥0∞} (B : ℝ≥0∞) (bound : ∀ c∈Icc (0:ℝ) 1,g c≤B) :
    (∫⁻ c,g c ∂unidad)≤B := by
  have q : (∫⁻ c,g c ∂unidad)≤∫⁻ _c : ℝ,B ∂unidad :=
    setLIntegral_mono' measurableSet_Icc bound
  simpa [lintegral_const,masa_unidad] using q

theorem levantar_diagonal (f : ℝ→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (z.1-z.2) ∂cuadrado) ≤ ∫⁻ d in Icc (-1:ℝ) 1,f d := by
  rw [cuadrado,lintegral_prod_symm (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ => f (z.1-z.2)) (hf.comp (measurable_fst.sub measurable_snd)).aemeasurable]
  apply integrar_cota; intro c hc
  simp only [sub_eq_add_neg]
  apply trasladar_fibra f hf (-c) _ measurableSet_Icc
  intro r hr
  change -1≤r+-c ∧ r+-c≤1
  obtain ⟨c0,c1⟩ := hc; obtain ⟨r0,r1⟩ := hr; constructor <;> linarith

theorem levantar_antidiagonal (f : ℝ→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (z.1+z.2) ∂cuadrado) ≤ ∫⁻ s in Icc (0:ℝ) 2,f s := by
  rw [cuadrado,lintegral_prod_symm (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ => f (z.1+z.2)) (hf.comp (measurable_fst.add measurable_snd)).aemeasurable]
  apply integrar_cota; intro c hc
  apply trasladar_fibra f hf c _ measurableSet_Icc
  intro r hr
  change 0≤r+c ∧ r+c≤2
  obtain ⟨c0,c1⟩ := hc; obtain ⟨r0,r1⟩ := hr; constructor <;> linarith
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.levantar_fila
#print axioms ArticuloA.Perfil.levantar_columna
#print axioms ArticuloA.Perfil.levantar_diagonal
#print axioms ArticuloA.Perfil.levantar_antidiagonal
