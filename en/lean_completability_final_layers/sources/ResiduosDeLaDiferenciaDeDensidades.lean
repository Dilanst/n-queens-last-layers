import SaltosDeLosCamposEnLaDensidad
import ResidualFisicoDeLasCuatroEcuaciones
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
theorem carga_de_una_diferencia {U V : ℝ×ℝ→ℝ} (uc : Continuous U) (vc : Continuous V) (i : Fin 3) (s : ℝ) :
    cargaDeFranja (fun z=>V z-U z) i s=cargaDeFranja V i s-cargaDeFranja U i s := by
  have cc : Continuous (columnaEnFibra i s) := by
    change Continuous (fun y=>columnaEnFibra i s y)
    fin_cases i <;> simp [columnaEnFibra] <;> fun_prop
  have slice {F : ℝ×ℝ→ℝ} (fc : Continuous F) : IntervalIntegrable (enLaFranja F i s) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have ic:=((fc.comp (continuous_id.prodMk cc)).intervalIntegrable (μ:=volume) (0:ℝ) 1)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at ic
    let S: Set ℝ:=(columnaEnFibra i s) ⁻¹' unidadCerrada
    have same : enLaFranja F i s=S.indicator (fun y=>F (y,columnaEnFibra i s y)) := by
      funext y; by_cases h : columnaEnFibra i s y∈unidadCerrada <;> simp [S,enLaFranja,Set.indicator_apply,h]
    rw [same]
    exact IntegrableOn.indicator ic (measurableSet_Icc.preimage cc.measurable)
  unfold cargaDeFranja
  rw [←intervalIntegral.integral_sub (slice vc) (slice uc)]
  apply intervalIntegral.integral_congr
  intro y _
  simp only [enLaFranja]; split_ifs <;> simp

theorem diferencia_de_las_ecuaciones_de_fila {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (t s : ℝ) :
    let U:=densidadExteriorB33 p x b
    let R:=filaExteriorB33 p x b
    (∫ c in (0:ℝ)..1,trasladaFilaB33 U t (s,c)-U (s,c))*saltoLogB33 R t s≤0 := by
  intro U R
  have uc:= (soporte_de_densidad_extendida h xn bp kp).1
  have sl (v : ℝ) : IntervalIntegrable (fun c=>U (v,c)) volume 0 1 :=
    (uc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable ..
  change ((∫ c in (0:ℝ)..1,U (s+t,c)-U (s,c))*_)≤0
  rw [intervalIntegral.integral_sub (sl (s+t)) (sl s)]
  have eq : (∫ c in (0:ℝ)..1,U (s+t,c))-(∫ c in (0:ℝ)..1,U (s,c))= -x*(R (s+t)-R s) := by
    change (∫ c in (0:ℝ)..1,densidadExteriorB33 p x b (s+t,c))-(∫ c in (0:ℝ)..1,densidadExteriorB33 p x b (s,c))=_
    dsimp only [R]
    linarith only [ecuacion_de_la_fila_en_toda_la_recta h xn bp kp (s+t),ecuacion_de_la_fila_en_toda_la_recta h xn bp kp s]
  rw [eq,mul_assoc]
  have pr : ∀ y,0<R y := fun y=>(one_div_pos.mpr (add_pos_of_nonneg_of_pos xn bp)).trans_le
    ((nucleo_y_fila_del_perfil h xn bp kp).2 y).1
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr xn) (signo_del_salto_de_log pr s t)

theorem diferencia_de_las_ecuaciones_oblicuas {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (t : ℝ) (i : Fin 3) (di : i≠0) {s : ℝ}
    (hs : s∈rangoF (familiaDeFranja i)) :
    let U:=densidadExteriorB33 p x b
    let v:=campoR15 p (familiaDeFranja i)
    |cargaDeFranja (fun z=>trasladaFilaB33 U t z-U z) i s+(v (s+t)-v s)|≤2*(b*(1/(x+b*κ^2))*M)*|t| := by
  intro U v
  have uc:Continuous U := (soporte_de_densidad_extendida h xn bp kp).1
  rw [carga_de_una_diferencia uc (continuidad_de_la_densidad_trasladada uc t)]
  have orig:=euler_en_la_franja_ampliada h i (s:=s) (fun hi=>(di hi).elim)
  simp only [terminoLibreB33,if_neg di,one_mul] at orig
  change cargaDeFranja U i s+v s=1 at orig
  have shifted : |cargaDeFranja (trasladaFilaB33 U t) i s+v (s+t)-1|≤2*(b*(1/(x+b*κ^2))*M)*|t| := by
    have bound:=(residual_fisico_de_fila_y_tres_fibras h xn bp kp t).2 (familiaDeFranja i) s hs
    dsimp only [v]
    fin_cases i
    · exact (di rfl).elim
    · simpa [familiaDeFranja,residualDeTraslacionB33,terminoLibreB33,trasladaFilaB33,U] using bound
    · simpa [familiaDeFranja,residualDeTraslacionB33,terminoLibreB33,trasladaFilaB33,U] using bound
  convert shifted using 2
  linarith only [orig]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.carga_de_una_diferencia
#print axioms ArticuloA.Historias.diferencia_de_las_ecuaciones_de_fila
#print axioms ArticuloA.Historias.diferencia_de_las_ecuaciones_oblicuas
