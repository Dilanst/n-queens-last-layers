import EnergiaEnLosIntervalosDelArticulo
import ResidualFisicoDeLasCuatroEcuaciones
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def logFisicoB33 (p : FactoresContinuos) (x b : ℝ) :=
  cuatroLogTrasladados (filaExteriorB33 p x b) (campoR15 p 1) (campoR15 p 2) (campoR15 p 3)
def factoresDeLogB33 (v : Fin 4→ℝ→ℝ) : FactoresContinuos :=
  let f i y : ℝ≥0:=⟨Real.exp (v i y),(Real.exp_pos _).le⟩
  ⟨f 0,f 1,f 2,f 3⟩
theorem factores_recuperados_por_exponencial (v : Fin 4→ℝ→ℝ) :
    camposFisicos (factoresDeLogB33 v)=fun i y=>Real.exp (v i y) := by
  funext i y; fin_cases i <;> rfl

theorem densidad_trasladada_en_coordenadas_log {p : FactoresContinuos} {x b : ℝ}
    (rp : ∀ s,0<filaExteriorB33 p x b s) (cp : ∀ s,0<campoR15 p 1 s)
    (dp : ∀ s,0<campoR15 p 2 s) (ap : ∀ s,0<campoR15 p 3 s) (t : ℝ) (z : ℝ×ℝ) :
    trasladaFilaB33 (densidadExteriorB33 p x b) t z=b*pesoContinuo (factoresDeLogB33 (logFisicoB33 p x b t)) z.1 z.2 := by
  dsimp [trasladaFilaB33,densidadExteriorB33,pesoContinuo,factoresDeLogB33,logFisicoB33,cuatroLogTrasladados]
  rw [Real.exp_log (rp _),Real.exp_log (cp _),Real.exp_log (dp _),Real.exp_log (ap _)]
  rw [show z.1+t-z.2=z.1-z.2+t by ring,show z.1+t+z.2=z.1+z.2+t by ring]; ring

theorem residual_igual_al_producto_por_cavidad {p : FactoresContinuos} {x b : ℝ}
    (rp : ∀ s,0<filaExteriorB33 p x b s) (cp : ∀ s,0<campoR15 p 1 s)
    (dp : ∀ s,0<campoR15 p 2 s) (ap : ∀ s,0<campoR15 p 3 s) (t : ℝ) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    let v:=logFisicoB33 p x b t
    Real.exp (v i s)*((if i.val<2 then x else 1)+b*cavidadFisica (fun j y=>Real.exp (v j y)) i s)=
      1+residualDeTraslacionB33 p x b t i s := by
  intro v
  let pt:=factoresDeLogB33 v
  let V:=trasladaFilaB33 (densidadExteriorB33 p x b) t
  have point (z : ℝ×ℝ) : V z=b*pesoContinuo pt z.1 z.2 := densidad_trasladada_en_coordenadas_log rp cp dp ap t z
  have proj (j : Fin 3) {y : ℝ} (hy : y∈rangoF (familiaDeFranja j)) :
      cargaDeFranja V j y=b*integralFisica pt (familiaDeFranja j) y := by
    rw [carga_de_franja_con_densidades_iguales (v:=fun z=>b*pesoContinuo pt z.1 z.2)
      (fun r _ c _=>point (r,c)),carga_de_franja_por_escalar,carga_en_la_etiqueta_fisica pt j hy]
  have row : (∫ c in (0:ℝ)..1,V (s,c))=b*integralFisica pt 0 s := by
    change _=b*∫ c in (0:ℝ)..1,pesoContinuo pt s c
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun c _=>point (s,c))
  have fact:=factor_de_la_familia_por_su_cavidad pt i s
  change integralFisica (factoresDeLogB33 v) i s=_ at fact
  dsimp only [pt] at fact
  rw [factores_recuperados_por_exponencial] at fact
  have eq : residualDeTraslacionB33 p x b t i s=b*integralFisica pt i s+
      (if i.val<2 then x else 1)*Real.exp (v i s)-1 := by
    fin_cases i
    · change (∫ c in (0:ℝ)..1,V (s,c))+_ -1=_
      rw [row]; simp [v,logFisicoB33,cuatroLogTrasladados,Real.exp_log (rp _)]
    · change cargaDeFranja V 0 s+_ -1=_
      rw [proj 0 hs]; simp [v,logFisicoB33,cuatroLogTrasladados,terminoLibreB33,familiaDeFranja,Real.exp_log (cp _)]
    · change cargaDeFranja V 1 s+_ -1=_
      rw [proj 1 hs]; simp [v,logFisicoB33,cuatroLogTrasladados,terminoLibreB33,familiaDeFranja,Real.exp_log (dp _)]
    · change cargaDeFranja V 2 s+_ -1=_
      rw [proj 2 hs]; simp [v,logFisicoB33,cuatroLogTrasladados,terminoLibreB33,familiaDeFranja,Real.exp_log (ap _)]
  rw [eq]; change _=1+(b*integralFisica (factoresDeLogB33 v) i s+_-1)
  rw [fact]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.factores_recuperados_por_exponencial
#print axioms ArticuloA.Historias.densidad_trasladada_en_coordenadas_log
#print axioms ArticuloA.Historias.residual_igual_al_producto_por_cavidad
