import CavidadDeUnaFibraFisica
import IntegralesEnIntervalosTransversales
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set MeasureTheory
open scoped Interval
def masaExterior (f : Fin 4→ℝ→ℝ) (g : Fin 4) :=
  ∫ y in extremoIzq g..extremoDer g,f g y

theorem integrable_sobre_intervalo {f : ℝ→ℝ} {a b : ℝ} (hab : a≤b)
    (hf : ContinuousOn f (Icc a b)) : IntervalIntegrable f volume a b :=
  (by simpa [uIcc_of_le hab] using hf : ContinuousOn f (uIcc a b)).intervalIntegrable

theorem masa_exterior_no_negativa {f : Fin 4→ℝ→ℝ} (hn : ∀ g y,0≤f g y) (g : Fin 4) :
    0≤masaExterior f g := intervalIntegral.integral_nonneg_of_forall (extremosF g) (hn g)

theorem masa_en_cuerda_fisica {f : Fin 4→ℝ→ℝ} (cf : ∀ g, ContinuousOn (f g) (rangoF g))
    (hn : ∀ g y,0≤f g y) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) (j : Fin 3) :
    (∫ t in (0:ℝ)..longitudDeCuerda i s,restriccionACuerda f i s t j) ≤
      masaExterior f (familiaTransversal i j) := by
  have hd:=longitud_en_unidad i hs
  have h0:=etiqueta_en_el_intervalo_fisico i j hs (show (0:ℝ)∈Icc 0 (longitudDeCuerda i s) from ⟨le_rfl,hd.1⟩)
  simp only [mul_zero,zero_add] at h0
  exact masa_no_aumenta_bajo_transversal (extremosF _) h0
    (etiqueta_en_el_intervalo_fisico i j hs ⟨hd.1,le_rfl⟩) (pendiente_absoluta_al_menos_uno i j)
    (hn _) (integrable_sobre_intervalo (extremosF _) (cf _))

theorem energia_en_cuerda_fisica {f : Fin 4→ℝ→ℝ} (cf : ∀ g, ContinuousOn (f g) (rangoF g))
    (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) (j : Fin 3) :
    (∫ t in (0:ℝ)..longitudDeCuerda i s,|restriccionACuerda f i s t j|) ≤
      Real.sqrt (masaExterior (fun g y=>f g y^2) (familiaTransversal i j)) := by
  have hd:=longitud_en_unidad i hs
  have h0:=etiqueta_en_el_intervalo_fisico i j hs (show (0:ℝ)∈Icc 0 (longitudDeCuerda i s) from ⟨le_rfl,hd.1⟩)
  simp only [mul_zero,zero_add] at h0
  exact masa_absoluta_desde_energia hd (extremosF _) h0
    (etiqueta_en_el_intervalo_fisico i j hs ⟨hd.1,le_rfl⟩) (pendiente_absoluta_al_menos_uno i j)
    (integrable_sobre_intervalo (extremosF _) ((cf _).pow 2))
    (integrable_sobre_intervalo hd.1 (campo_continuo_sobre_la_cuerda cf i hs j).abs)
    (integrable_sobre_intervalo hd.1 ((campo_continuo_sobre_la_cuerda cf i hs j).pow 2))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integrable_sobre_intervalo
#print axioms ArticuloA.Historias.masa_exterior_no_negativa
#print axioms ArticuloA.Historias.masa_en_cuerda_fisica
#print axioms ArticuloA.Historias.energia_en_cuerda_fisica
