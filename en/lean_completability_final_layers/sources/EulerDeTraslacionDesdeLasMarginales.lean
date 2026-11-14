import CamposNormalizadosParaLaTraslacion
import EulerEnFibrasSinConstanteLipschitz
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
theorem datos_de_traslacion_desde_marginales {p : FactoresContinuos} (x : ℝ≥0) {b κ M : ℝ}
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i))
    (di : ∀ i : Fin 4, 2 ≤ i.val → ∀ s∈rangoF i,κ≤camposFisicos p i s ∧ camposFisicos p i s≤1)
    (col : ∀ s∈unidadCerrada,(p.columna s:ℝ)≤M)
    (normCol : (∫ s in (0:ℝ)..1,(p.columna s:ℝ))=1)
    (ae : ∀ i,∀ᵐ s ∂marginalRef i,b*integralFisica p i s=1-holguraLinea p x i s) :
    DatosTraslacionFisica p x b κ M := by
  refine ⟨cp,di,col,normCol,?_⟩
  intro i s hs
  have e:=ecuacion_puntual_sin_lipschitz x cp i (ae i) s hs
  rw [factor_de_la_familia_por_su_cavidad]
  linarith only [e]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.datos_de_traslacion_desde_marginales
