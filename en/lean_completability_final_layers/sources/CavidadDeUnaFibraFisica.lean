import GeometriaDeLasTresTransversales
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set MeasureTheory
open scoped Interval
def etiquetaEnCuerda (i : Fin 4) (j : Fin 3) (s t : ℝ) :=
  pendienteTransversal i j*t+coord (familiaTransversal i j) (puntoDeCuerda i s 0)

def restriccionACuerda (p : Fin 4→ℝ→ℝ) (i : Fin 4) (s t : ℝ) (j : Fin 3) :=
  p (familiaTransversal i j) (etiquetaEnCuerda i j s t)

def productoEnCuerda (p : Fin 4→ℝ→ℝ) (i : Fin 4) (s t : ℝ) :=
  let a:=restriccionACuerda p i s t
  a 0*a 1*a 2

def cavidadFisica (p : Fin 4→ℝ→ℝ) (i : Fin 4) (s : ℝ) :=
  ∫ t in (0:ℝ)..longitudDeCuerda i s,productoEnCuerda p i s t

def camposFisicos (p : FactoresContinuos) (i : Fin 4) (s : ℝ) : ℝ := factorF p i s

private theorem producto_por_familias (p : FactoresContinuos) (i : Fin 4) (z : ℝ×ℝ) :
    pesoContinuo p z.1 z.2 = camposFisicos p i (coord i z)*
      (camposFisicos p (familiaTransversal i 0) (coord (familiaTransversal i 0) z)*
       camposFisicos p (familiaTransversal i 1) (coord (familiaTransversal i 1) z)*
       camposFisicos p (familiaTransversal i 2) (coord (familiaTransversal i 2) z)) := by
  fin_cases i <;> simp [camposFisicos,factorF,pesoContinuo,coord,familiaTransversal] <;> ring

theorem factor_de_la_familia_por_su_cavidad (p : FactoresContinuos) (i : Fin 4) (s : ℝ) :
    integralFisica p i s=camposFisicos p i s*cavidadFisica (camposFisicos p) i s := by
  have same : integralFisica p i s=∫ t in (0:ℝ)..longitudDeCuerda i s,
      pesoContinuo p (puntoDeCuerda i s t).1 (puntoDeCuerda i s t).2 := by fin_cases i <;> rfl
  rw [same,cavidadFisica,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [productoEnCuerda,restriccionACuerda,etiquetaEnCuerda,←coordenada_transversal_afin,
    coordenada_de_la_familia_fijada] using producto_por_familias p i (puntoDeCuerda i s t)

theorem etiqueta_continua (i : Fin 4) (j : Fin 3) (s : ℝ) :
    Continuous (etiquetaEnCuerda i j s) :=
  (continuous_const.mul continuous_id).add continuous_const

theorem campo_continuo_sobre_la_cuerda {p : Fin 4→ℝ→ℝ}
    (hp : ∀ g,ContinuousOn (p g) (rangoF g)) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) (j : Fin 3) :
    ContinuousOn (fun t=>restriccionACuerda p i s t j) (Icc 0 (longitudDeCuerda i s)) :=
  (hp _).comp (etiqueta_continua i j s).continuousOn (fun _ ht=>etiqueta_en_el_intervalo_fisico i j hs ht)

theorem producto_continuo_sobre_la_cuerda {p : Fin 4→ℝ→ℝ}
    (hp : ∀ g,ContinuousOn (p g) (rangoF g)) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    ContinuousOn (productoEnCuerda p i s) (Icc 0 (longitudDeCuerda i s)) :=
  ((campo_continuo_sobre_la_cuerda hp i hs 0).mul (campo_continuo_sobre_la_cuerda hp i hs 1)).mul
    (campo_continuo_sobre_la_cuerda hp i hs 2)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.factor_de_la_familia_por_su_cavidad
#print axioms ArticuloA.Historias.etiqueta_continua
#print axioms ArticuloA.Historias.campo_continuo_sobre_la_cuerda
#print axioms ArticuloA.Historias.producto_continuo_sobre_la_cuerda
