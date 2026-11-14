import CamposNormalizadosParaLaTraslacion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def traspuestoB33 (p : FactoresContinuos) : FactoresContinuos :=
  ⟨p.columna,p.fila,fun s=>p.diagonal (-s),p.anti⟩

theorem densidad_del_traspuesto (p : FactoresContinuos) (r c : ℝ) :
    pesoContinuo (traspuestoB33 p) r c=pesoContinuo p c r := by
  simp only [traspuestoB33,pesoContinuo,neg_sub,add_comm r c]
  ring

theorem integral_oblicua_del_traspuesto (p : FactoresContinuos) (s : ℝ) (anti : Bool) :
    integralDesplazada (traspuestoB33 p) s anti=integralDesplazada p (if anti then s else -s) anti := by
  cases anti
  · simp only [integralDesplazada,Bool.false_eq_true,if_false,abs_neg,neg_neg,densidad_del_traspuesto]
  · simp only [integralDesplazada,if_true,densidad_del_traspuesto]
    let len:=1-|s|
    let f:=fun y=>pesoContinuo p (max s 0+y) (1-(max (-s) 0+y))
    have flip : (∫ t in (0:ℝ)..len,f (len-t))=∫ t in (0:ℝ)..len,f t := by
      rw [intervalIntegral.integral_comp_sub_left]; simp
    calc
      _ = (∫ t in (0:ℝ)..len,f (len-t)) := by
        apply intervalIntegral.integral_congr; intro t _
        have h : max s 0 + max (-s) 0=|s| := by
          rcases le_total 0 s with pos|neg
          · simp [max_eq_left pos,max_eq_right (neg_nonpos.mpr pos),abs_of_nonneg pos]
          · simp [max_eq_right neg,max_eq_left (neg_nonneg.mpr neg),abs_of_nonpos neg]
        dsimp only [f,len]
        congr 1 <;> linarith only [h]
      _ = _ := flip

theorem datos_fisicos_del_traspuesto {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (rowUpper : ∀ s∈unidadCerrada,(p.fila s:ℝ)≤m) (rowMass : (∫ s in (0:ℝ)..1,(p.fila s:ℝ))=1) :
    DatosTraslacionFisica (traspuestoB33 p) x b κ m := by
  have reflect : MapsTo (fun y : ℝ=> -y) (rangoF 2) (rangoF 2) := by
    intro y hy; change -1≤y ∧ y≤1 at hy; change -1≤ -y ∧ -y≤1
    constructor <;> linarith [hy.1,hy.2]
  refine ⟨?_,?_,rowUpper,rowMass,?_⟩
  · intro i; fin_cases i
    · exact h.continuos 1
    · exact h.continuos 0
    · exact (h.continuos 2).comp continuous_neg.continuousOn reflect
    · exact h.continuos 3
  · intro i hi s hs
    rcases (show i=2 ∨ i=3 by omega) with rfl|rfl
    · exact h.diagonal 2 (by decide) _ (reflect hs)
    · exact h.diagonal 3 (by decide) _ hs
  · intro i s hs
    fin_cases i
    · change b*(∫ c in (0:ℝ)..1,pesoContinuo (traspuestoB33 p) s c)+x*(p.columna s:ℝ)=1
      simp only [densidad_del_traspuesto]; exact h.euler 1 s hs
    · change b*(∫ c in (0:ℝ)..1,pesoContinuo (traspuestoB33 p) c s)+x*(p.fila s:ℝ)=1
      simp only [densidad_del_traspuesto]; exact h.euler 0 s hs
    · change b*integralDesplazada (traspuestoB33 p) s false+1*(p.diagonal (-s):ℝ)=1
      rw [integral_oblicua_del_traspuesto]; exact h.euler 2 (-s) (reflect hs)
    · change b*integralDesplazada (traspuestoB33 p) (s-1) true+1*(p.anti s:ℝ)=1
      rw [integral_oblicua_del_traspuesto]; exact h.euler 3 s hs
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.densidad_del_traspuesto
#print axioms ArticuloA.Historias.integral_oblicua_del_traspuesto
#print axioms ArticuloA.Historias.datos_fisicos_del_traspuesto
