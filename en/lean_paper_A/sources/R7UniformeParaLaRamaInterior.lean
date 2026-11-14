import HolgurasFisicasParaElBalanceLogaritmico
import SueloEntropicoDeLaComparacionR5
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Real
open scoped Topology
def masaLogOblicua (p : FactoresContinuos) (x : ℝ≥0) (i : Fin 4) :=
  ∫ s,-log (holguraInteriorR5 p x i s) ∂marginalRef i

theorem aporte_de_una_diagonal_R7 {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (ob : 2 ≤ i.val) :
    (1/10:ℝ)/2*masaLogOblicua p x i≤ -terminoDeR5 P p x i+2*((1+(1/10:ℝ)/2)*log (2/(1/10:ℝ))) := by
  let u:=holguraInteriorR5 p x i
  let δ:=1-(x:ℝ)
  obtain ⟨uc,up,w,occ,u1⟩:=vacancia_fisica_y_logaritmo e xp cp pos i
  have mrange {s : ℝ} (hs : s∈rangoF i) : 0≤marginalDelTestigo i s ∧ marginalDelTestigo i s≤9/10 := by
    fin_cases i
    · exact False.elim (by norm_num at ob)
    · exact False.elim (by norm_num at ob)
    · exact rango_del_testigo_sobre_una_oblicua false (abs_le.mpr hs)
    · change 0≤s ∧ s≤2 at hs
      exact rango_del_testigo_sobre_una_oblicua true (abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  have ref : (marginalRef i).real univ=2 := by
    fin_cases i
    · exact False.elim (by norm_num at ob)
    · exact False.elim (by norm_num at ob)
    · norm_num [marginalRef,measureReal_def,Real.volume_Ioc]
    · norm_num [marginalRef,measureReal_def,Real.volume_Ioc]
  have lc:=uc.log (fun s=>(up s).ne')
  have mi:=continua_la_marginal_del_testigo i
  have ri : Continuous (fun s=>(1-u s-δ*marginalDelTestigo i s)*(-log (u s))) :=
    ((continuous_const.sub uc).sub (continuous_const.mul mi)).mul lc.neg
  have bounds : ∀ᵐ s ∂marginalRef i,0<u s ∧ u s≤1 ∧ 0≤marginalDelTestigo i s ∧ marginalDelTestigo i s≤1-(1/10:ℝ) := by
    filter_upwards [u1,linea_en_dominio i] with s hi hs
    obtain ⟨lo,top⟩:=mrange hs
    exact ⟨up s,hi,lo,by linarith⟩
  have bound:=integral_oblicua_desde_la_comparacion (marginalRef i) (δ:=δ)
    (by norm_num : (0:ℝ)<1/10) (by norm_num) (by dsimp [δ]; linarith [x.coe_nonneg]) bounds
    (integral_de_etiqueta_de_una_continua i lc.neg) (integral_de_etiqueta_de_una_continua i ri)
  have key : (∫ s,(1-u s-δ*marginalDelTestigo i s)*(-log (u s)) ∂marginalRef i) = -terminoDeR5 P p x i := by
    unfold terminoDeR5; rw [←integral_neg]
    apply integral_congr_ae
    filter_upwards [occ] with s h
    rw [h,w]; dsimp only [u,δ]; ring
  rw [key,ref] at bound
  exact bound

/-- The bound uses only per-parameter continuity and positivity. The right hand side is independent of x. -/
theorem cota_R7_desde_euler_en_un_parametro {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (x1 : (x:ℝ)≤1)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    masaLogOblicua p x 2+masaLogOblicua p x 3 ≤
      (2/(1/10:ℝ))*(6/5+1/exp 1+4*log (2/(1/10:ℝ)))+4*log (2/(1/10:ℝ)) := by
  have work:=comparacion_R5_desde_euler_interior e xp cp pos
  rw [Fin.sum_univ_four] at work
  exact constante_R7_para_las_dos_oblicuas (by norm_num : (0:ℝ)<1/10)
    (by linarith only [work]) (suelo_entropico_R5 e x1 cp pos)
    (covarianza_en_cada_transversal e xp cp pos 0 (by decide)) (covarianza_en_cada_transversal e xp cp pos 1 (by decide))
    (aporte_de_una_diagonal_R7 e xp cp pos 2 (by decide)) (aporte_de_una_diagonal_R7 e xp cp pos 3 (by decide))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.aporte_de_una_diagonal_R7
#print axioms ArticuloA.Historias.cota_R7_desde_euler_en_un_parametro
