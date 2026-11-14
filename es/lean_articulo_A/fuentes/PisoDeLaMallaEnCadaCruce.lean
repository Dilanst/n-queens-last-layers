import MasaGeometricaDeLasFuentes
import ConcentracionFisicaEnElUltimoReloj
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem cuatro_holguras_del_cruce {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 0<n) (sp : ControlEspacial p κ m L) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z e : Cell n) :
    (κ/2)^4 ≤ masas.four (fun j => 1-cargaDeDestino h p z e j) := by
  have each (j : Fin 4) : κ/2 ≤ 1-cargaDeDestino h p z e j := by
    let i:=side j
    let v : Indice n:=⟨key z e j,on_board (dest z e j) (side j)⟩
    have ob : 2 ≤ i.val := by change 2 ≤ (side j).val; fin_cases j <;> decide
    have t:=carga_estricta_en_oblicuas hn sp i v ob margen (bal i v)
    have r : (cargaDeDestino h p z e j:ℝ)≤1-(κ:ℝ)/2 := by
      change (probLinea n h p (i,v.val):ℝ)≤_
      rwa [carga_identificada hn]
    apply le_tsub_of_add_le_left
    exact_mod_cast (show (cargaDeDestino h p z e j:ℝ)+(κ:ℝ)/2≤1 by linarith)
  have step:=four_mono masas (v:=fun _ => κ/2) (w:=fun j => 1-cargaDeDestino h p z e j) each
  exact (show (κ/2)^4=masas.four (fun _ => κ/2) by change _ = (κ/2*(κ/2))*(κ/2*(κ/2)); ring).le.trans step

theorem piso_de_la_malla {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z : Cell n) :
    (((↑(n-h):ℝ)-4*((m:ℝ)^4/κ^4))*((κ:ℝ)/2)^4)≤(blancoFinalDeMalla h p z:ℝ) := by
  let π:=probDeLaCasilla (n:=n) h p
  let cut (e : Cell n) := if filterG z e then 0 else π e
  let keep (e : Cell n) := if filterG z e then π e else 0
  let c:ℝ≥0:=(κ/2)^4
  have splitMass (l : List (Cell n)) : masas.sum l keep+masas.sum l cut=masas.sum l π := by
    induction l with
    | nil => change (0:ℝ≥0)+0=0; exact zero_add 0
    | cons e l ih =>
      change (keep e+masas.sum l keep)+(cut e+masas.sum l cut)=π e+masas.sum l π
      rw [←ih]; have term : keep e+cut e=π e := by by_cases g : filterG z e <;> simp [g,keep,cut]
      rw [←term]; ac_rfl
  have floor : masas.sum (board n) keep*c≤blancoFinalDeMalla h p z := by
    rw [←show masas.sum (board n) (fun e => keep e*c)=masas.sum (board n) keep*c from Cart.sum_scale masas _ _ c]
    unfold blancoFinalDeMalla blancoDeLaRaiz
    apply MassScale.sum_mono masas.toMassScale; intro e _
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (cuatro_holguras_del_cruce (by omega) sp bal margen z e) (zero_le (keep e))
  have total:=splitMass (board n)
  rw [show masas.sum (board n) π=↑(n-h) from masa_exacta_de_fuentes p (by omega) sp kp] at total
  have cap:=masa_descartada_por_cruce z π _ (cargas_para_un_cruce hn sp kp bal margen z).2
  change masas.sum (board n) cut ≤ 4*(m^4/κ^4) at cap
  have mass : (masas.sum (board n) keep:ℝ)+(masas.sum (board n) cut:ℝ)=(↑(n-h):ℝ) := by simpa only [NNReal.coe_add,NNReal.coe_natCast] using congrArg NNReal.toReal total
  have disc : (masas.sum (board n) cut:ℝ)≤4*((m:ℝ)^4/κ^4) := by exact_mod_cast cap
  apply le_trans (mul_le_mul_of_nonneg_right (by linarith only [mass,disc] :
    (↑(n-h):ℝ)-4*((m:ℝ)^4/κ^4)≤(masas.sum (board n) keep:ℝ)) (by positivity))
  exact_mod_cast floor
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.piso_de_la_malla
