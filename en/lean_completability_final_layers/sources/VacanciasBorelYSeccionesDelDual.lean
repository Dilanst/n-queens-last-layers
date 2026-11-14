import CompetidoresBorelDeLaCajaDual
import LeyDeImagenDesdePruebasBorel
import ContinuidadDeLasCuatroCavidadesMedibles
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Classical
def vacanciaDeCampo (g : Fin 4→ℝ→ℝ) (i : Fin 4) : ℝ→ℝ :=
  (rangoF i).indicator (fun s=>exp (-g i s))

theorem vacancia_de_campo_medible {g : Fin 4→ℝ→ℝ} (gm : ∀ i,Measurable (g i)) (i : Fin 4) :
    Measurable (vacanciaDeCampo g i) := ((gm i).neg.exp).indicator measurableSet_Icc

theorem vacancia_de_campo_en_unidad {H : ℝ} {g : Fin 4→ℝ→ℝ} (gb : ∀ i s,g i s∈Icc 0 H) (i : Fin 4) (s : ℝ) :
    vacanciaDeCampo g i s∈Icc 0 1 := by
  by_cases hs : s∈rangoF i
  · rw [vacanciaDeCampo,indicator_of_mem hs]; exact ⟨(exp_pos _).le,exp_le_one_iff.mpr (neg_nonpos.mpr (gb i s).1)⟩
  · simp [vacanciaDeCampo,hs]

theorem vacancia_de_campo_integrable {H : ℝ} {g : Fin 4→ℝ→ℝ} (gm : ∀ i,Measurable (g i))
    (gb : ∀ i s,g i s∈Icc 0 H) (i : Fin 4) : Integrable (vacanciaDeCampo g i) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  have const : IntegrableOn (fun _ : ℝ=> (1:ℝ)) (rangoF i) := integrableOn_const.mpr (.inr (measure_Icc_lt_top (μ:=volume)))
  apply const.mono' (gm i).neg.exp.aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
  exact exp_le_one_iff.mpr (neg_nonpos.mpr (gb i s).1)

theorem particion_en_producto_crudo {H : ℝ} (u : CajaDual H) {g : Fin 4→ℝ→ℝ}
    (gm : ∀ i,Measurable (g i)) (eq : ∀ i,campoDual u i=ᵐ[marginalRef i] g i) :
    particionDual u=∫ z,productoCuatroFisico (vacanciaDeCampo g) z ∂cuadrado := by
  apply integral_congr_ae
  filter_upwards [suma_dual_sobre_representantes u gm eq,tablero_en_dominio] with z hz inside
  have coordIn:=coordenadas_en_dominio inside
  rw [hz,Fin.sum_univ_four]
  simp only [productoCuatroFisico,vacanciaDeCampo,indicator_of_mem (coordIn _),neg_add_rev,exp_add]
  ring

theorem particion_en_una_fibra {H : ℝ} (u : CajaDual H) {g : Fin 4→ℝ→ℝ}
    (gm : ∀ i,Measurable (g i)) (gb : ∀ i s,g i s∈Icc 0 H)
    (eq : ∀ i,campoDual u i=ᵐ[marginalRef i] g i) (i : Fin 4) :
    particionDual u=∫ s,exp (-g i s)*cavidadFisica (vacanciaDeCampo g) i s ∂marginalRef i := by
  rw [particion_en_producto_crudo u gm eq]
  have id:=adjuncion_del_producto_crudo (vacancia_de_campo_en_unidad gb) (vacancia_de_campo_medible gm) i
    (w:=fun _=>1) measurable_const (fun _=>by simp)
  simp only [mul_one] at id
  apply id.trans; apply integral_congr_ae
  filter_upwards [linea_en_dominio i] with s hs
  rw [vacanciaDeCampo,indicator_of_mem hs]

theorem misma_cavidad_fuera_de_una_etiqueta {g v : Fin 4→ℝ→ℝ} (i : Fin 4) (h : ∀ j,j≠i → g j=v j) (s : ℝ) :
    cavidadFisica (vacanciaDeCampo g) i s=cavidadFisica (vacanciaDeCampo v) i s := by
  have other (j : Fin 3) : familiaTransversal i j≠i := by fin_cases i <;> fin_cases j <;> decide
  have eq (j : Fin 3) : vacanciaDeCampo g (familiaTransversal i j)=vacanciaDeCampo v (familiaTransversal i j) := by
    unfold vacanciaDeCampo; rw [h _ (other j)]
  simp only [cavidadFisica,productoEnCuerda,restriccionACuerda,eq]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.vacancia_de_campo_medible
#print axioms ArticuloA.Historias.vacancia_de_campo_en_unidad
#print axioms ArticuloA.Historias.vacancia_de_campo_integrable
#print axioms ArticuloA.Historias.particion_en_producto_crudo
#print axioms ArticuloA.Historias.particion_en_una_fibra
#print axioms ArticuloA.Historias.misma_cavidad_fuera_de_una_etiqueta
