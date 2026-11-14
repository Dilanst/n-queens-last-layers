import CavidadesTransversalesYBandas
import BalanceEntropicoDeLasMedias
import CotasEscalaresDesdeLasMediasGeometricas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def constanteLogDEF35 : ℝ := (2/(1/10:ℝ))*(6/5+1/exp 1+4*log (2/(1/10:ℝ)))+4*log (2/(1/10:ℝ))
def techoDEF35 : ℝ := exp constanteLogDEF35

theorem techoDEF35_al_menos_uno : 1≤techoDEF35 := by
  apply one_le_exp
  have hl : 0≤log (2/(1/10:ℝ)) := log_nonneg (by norm_num)
  unfold constanteLogDEF35
  positivity

theorem cotas_de_euler_por_transversal {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (x1 : (x:ℝ)≤1)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (col : Bool) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
    let j:=indiceTransversal (!col)
    let y:=campoR15 p (indiceTransversal col) s
    (x:ℝ)+b*mediaGeometrica (campoR15 p j)/techoDEF35≤1/y ∧ 1/y≤(x:ℝ)+b := by
  have dom : s∈rangoF (indiceTransversal col) := by cases col <;> exact hs
  have eq:=euler_reciproco_de_la_fibra e cp pos (indiceTransversal col) s dom
  have rc : (indiceTransversal col).val<2 := by cases col <;> decide
  rw [coefLinea,if_pos rc] at eq
  dsimp only
  rw [campo_dentro_de_su_intervalo p _ dom,eq]
  obtain ⟨lb,ub⟩:=limites_de_la_cavidad_transversal e xp cp pos col s hs
  have r7 : costoTotalR7 p x≤constanteLogDEF35 := cota_R7_desde_euler_en_un_parametro e xp x1 cp pos
  let g:=mediaGeometrica (campoR15 p (indiceTransversal (!col)))
  have gp : 0<g := exp_pos _
  have ea : 1/techoDEF35≤exp (-costoTotalR7 p x) := by
    rw [one_div,techoDEF35,←exp_neg]
    exact exp_le_exp.mpr (neg_le_neg r7)
  have ls : g*(1/techoDEF35)≤cavidadFisica (camposFisicos p) (indiceTransversal col) s :=
    (mul_le_mul_of_nonneg_left ea gp.le).trans lb
  constructor
  · apply add_le_add_left
    simpa only [div_eq_mul_inv,one_mul,mul_assoc] using mul_le_mul_of_nonneg_left ls e.coef.le
  · simpa only [mul_one] using add_le_add_left (mul_le_mul_of_nonneg_left ub e.coef.le) (x:ℝ)

theorem cotas_para_las_medias_fisicas {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (x1 : (x:ℝ)≤1)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (col : Bool) : b*mediaGeometrica (campoR15 p (indiceTransversal (!col)))≤(1-(x:ℝ))*techoDEF35 := by
  let i:=indiceTransversal col
  let r:=campoR15 p i
  let g:=mediaGeometrica (campoR15 p (indiceTransversal (!col)))
  let d:=(x:ℝ)+b*g/techoDEF35
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  have ri : Integrable r unidad := (campo_continuo_por_recorte cp i).continuousOn.integrableOn_Icc
  have norm:=normalizacion_R15_en_masa_interior e xp i (by cases col <;> decide)
  have support : ∀ᵐ s ∂unidad,s∈Icc (0:ℝ) 1 := ae_restrict_mem measurableSet_Icc
  have bound : ∀ᵐ s ∂unidad,d*r s≤1 := by
    filter_upwards [support] with s hs
    exact (le_div_iff₀ (pos i _ (recorte_dentro i s))).mp (cotas_de_euler_por_transversal e xp x1 cp pos col s hs).1
  have integ:=integral_mono_ae (ri.const_mul d) (integrable_const (1:ℝ)) bound
  change (∫ s,d*r s ∂unidad)≤∫ _ : ℝ,(1:ℝ) ∂unidad at integ
  rw [integral_const_mul,show (∫ s,r s ∂unidad)=1 from norm,mul_one] at integ
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at integ
  have ee : 0<techoDEF35 := exp_pos _
  exact (div_le_iff₀ ee).mp (show b*g/techoDEF35≤1-(x:ℝ) by dsimp [d] at integ; linarith only [integ])

theorem bandas_fisicas_de_las_medias {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (d : 0<1-(x:ℝ))
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    let R:=mediaGeometrica (campoR15 p 0)
    let C:=mediaGeometrica (campoR15 p 1)
    1-(x:ℝ)≤b ∧ b≤(1-(x:ℝ))*techoDEF35^2 ∧ 1/techoDEF35≤R ∧ 1/techoDEF35≤C ∧
    1-(x:ℝ)≤b*R ∧ 1-(x:ℝ)≤b*C := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  have ub (i : Fin 4) (hi : i.val<2) : mediaGeometrica (campoR15 p i)≤1 := by
    have norm:=normalizacion_R15_en_masa_interior e xp i hi
    have cc:=campo_continuo_por_recorte cp i
    have pp s : 0<campoR15 p i s := pos i _ (recorte_dentro i s)
    have h:=jensen_log_en_una_probabilidad (μ:=unidad) (Eventually.of_forall pp) cc.continuousOn.integrableOn_Icc
      (cc.log (fun s=>(pp s).ne')).continuousOn.integrableOn_Icc (norm ▸ zero_lt_one)
    exact h.trans norm.le
  have x1 : (x:ℝ)≤1 := by linarith only [d]
  exact bandas_de_las_medias d e.coef.le (exp_pos _).le (exp_pos _).le (ub 0 (by decide)) (ub 1 (by decide))
    techoDEF35_al_menos_uno (cotas_para_las_medias_fisicas e xp x1 cp pos true)
    (cotas_para_las_medias_fisicas e xp x1 cp pos false) (masa_acotada_por_las_dos_medias e xp d cp pos)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.techoDEF35_al_menos_uno
#print axioms ArticuloA.Historias.cotas_de_euler_por_transversal
#print axioms ArticuloA.Historias.cotas_para_las_medias_fisicas
#print axioms ArticuloA.Historias.bandas_fisicas_de_las_medias
