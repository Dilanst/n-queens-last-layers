import MasaYEnergiaDeUnaCuerda
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
private theorem continuaExtension {p : Fin 4→ℝ→ℝ} (cp : ∀ g,ContinuousOn (p g) (rangoF g)) (g : Fin 4) :
    Continuous (fun y=>p g (recorte g y)) :=
  (cp g).comp_continuous (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro g)

private theorem etiquetaDosVariables (i : Fin 4) (j : Fin 3) :
    Continuous (Function.uncurry (etiquetaEnCuerda i j)) := by
  change Continuous (fun z : ℝ×ℝ=>etiquetaEnCuerda i j z.1 z.2)
  unfold etiquetaEnCuerda
  fin_cases i <;> fin_cases j <;>
    simp [pendienteTransversal,familiaTransversal,puntoDeCuerda,coord] <;> fun_prop

theorem cavidad_continua_con_factores_continuos {p : Fin 4→ℝ→ℝ}
    (cp : ∀ g,ContinuousOn (p g) (rangoF g)) (i : Fin 4) : ContinuousOn (cavidadFisica p i) (rangoF i) := by
  let q:=fun g y=>p g (recorte g y)
  have each (j : Fin 3) : Continuous (fun z : ℝ×ℝ =>restriccionACuerda q i z.1 z.2 j) :=
    (continuaExtension cp _).comp (etiquetaDosVariables i j)
  have integrand : Continuous (Function.uncurry (productoEnCuerda q i)) := ((each 0).mul (each 1)).mul (each 2)
  have len : Continuous (longitudDeCuerda i) := by
    change Continuous (fun s=>longitudDeCuerda i s)
    unfold longitudDeCuerda
    fin_cases i <;> simp [desplazamientoOblicuo] <;> fun_prop
  have gc:=intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ:=volume)
    (a₀:=(0:ℝ)) integrand len
  apply gc.continuousOn.congr
  intro s hs
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (longitud_en_unidad i hs).1] at ht
  have eq (j : Fin 3) : restriccionACuerda p i s t j=restriccionACuerda q i s t j := by
    unfold restriccionACuerda; dsimp only [q]
    exact congrArg (p _) (recorte_fijo _ (s:=etiquetaEnCuerda i j s t)
      (etiqueta_en_el_intervalo_fisico i j hs ht)).symm
  simp only [productoEnCuerda,eq]

theorem ecuacion_puntual_sin_lipschitz {p : FactoresContinuos} {b : ℝ} (x : ℝ≥0)
    (cp : ∀ g,ContinuousOn (camposFisicos p g) (rangoF g)) (i : Fin 4)
    (ae : ∀ᵐ t ∂marginalRef i,b*integralFisica p i t=1-holguraLinea p x i t) :
    ∀ t∈rangoF i,camposFisicos p i t*((if i.val<2 then (x:ℝ) else 1)+b*cavidadFisica (camposFisicos p) i t)=1 := by
  let d : ℝ:=if i.val<2 then (x:ℝ) else 1
  have ndeg : extremoIzq i≠extremoDer i := by fin_cases i <;> norm_num [extremoIzq,extremoDer]
  have ref : marginalRef i=volume.restrict (rangoF i) := by
    have eq : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [eq]; exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  have h : ∀ᵐ t ∂volume.restrict (rangoF i),camposFisicos p i t*(d+b*cavidadFisica (camposFisicos p) i t)=1 := by
    rw [ref] at ae
    filter_upwards [ae] with t ht
    rw [factor_de_la_familia_por_su_cavidad] at ht
    change b*(camposFisicos p i t*_) = 1-d*camposFisicos p i t at ht
    linarith only [ht]
  exact fun _ ht=>Measure.eqOn_Icc_of_ae_eq (μ:=volume) ndeg h ((cp i).mul
    (continuousOn_const.add (continuousOn_const.mul (cavidad_continua_con_factores_continuos cp i))))
    continuousOn_const ht
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cavidad_continua_con_factores_continuos
#print axioms ArticuloA.Historias.ecuacion_puntual_sin_lipschitz
