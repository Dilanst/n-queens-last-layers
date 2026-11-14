import LasCuatroHolgurasEnLosCentros
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Limites Corte Repair
noncomputable section
open Classical

theorem suma_fisica_del_tablero {n} (v : Cell n→ℝ≥0) :
    (masas.sum (board n) v:ℝ)=∑ e : Cell n,(v e:ℝ) := by
  have all : (board n).toFinset=Finset.univ := by ext e; simp [board_complete]
  simpa only [all] using suma_de_pesos_local _ (board_unique n) v

def factorEnCentros {n} (p : FactoresContinuos) (z e : Cell n) : ℝ :=
  factorDelCruce p (medio n z.1.val) (medio n z.2.val) (medio n e.1.val) (medio n e.2.val)

def sumaSinFiltro {n} (h : ℕ) (p : FactoresContinuos) (z : Cell n) : ℝ :=
  ∑ e : Cell n,(probDeLaCasilla h p e:ℝ)*factorEnCentros p z e

theorem error_del_descarte_y_producto {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z : Cell n) :
    |(blancoFinalDeMalla h p z:ℝ)-sumaSinFiltro h p z|≤
      4*(m:ℝ)^3*C+4*((m:ℝ)^4/κ^4)*(m:ℝ)^4 := by
  let π:=probDeLaCasilla (n:=n) h p
  let u:=fun e => holguraDeLaMalla h p z e
  let H:=factorEnCentros p z
  let D:=4*(m:ℝ)^3*((C:ℝ)/n)
  let cut:=fun e => if filterG z e then (0:ℝ≥0) else π e
  have err (e : Cell n) : |((if filterG z e then π e else 0)*u e:ℝ≥0)-((π e:ℝ)*H e)|≤
      (π e:ℝ)*D+(cut e:ℝ)*(m:ℝ)^4 := by
    by_cases g : filterG z e
    · simp only [g,if_true,NNReal.coe_mul,cut,NNReal.coe_zero,zero_mul,add_zero,←mul_sub,abs_mul,
        abs_of_nonneg (NNReal.coe_nonneg _)]
      exact mul_le_mul_of_nonneg_left (diferencia_del_producto hn sp kp m1 bal margen z e) (NNReal.coe_nonneg _)
    · simp only [g,if_false,zero_mul,NNReal.coe_zero,zero_sub,abs_neg,abs_mul,cut,
        abs_of_nonneg (NNReal.coe_nonneg _)]
      have cap:=factor_acotado sp (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
        (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
      apply (mul_le_mul_of_nonneg_left cap (NNReal.coe_nonneg (π e))).trans
      exact le_add_of_nonneg_left (by dsimp [D]; positivity)
  have mass : (∑ e : Cell n,(π e:ℝ))=(↑(n-h):ℝ) := by
    rw [←suma_fisica_del_tablero,masa_exacta_de_fuentes p (by omega) sp kp,NNReal.coe_natCast]
  have lost : (∑ e : Cell n,(cut e:ℝ))≤4*((m:ℝ)^4/κ^4) := by
    rw [←suma_fisica_del_tablero]
    exact_mod_cast masa_descartada_por_cruce z π _ (cargas_para_un_cruce hn sp kp bal margen z).2
  have mesh : (blancoFinalDeMalla h p z:ℝ)=∑ e : Cell n,(((if filterG z e then π e else 0)*u e:ℝ≥0):ℝ) := by
    unfold blancoFinalDeMalla blancoDeLaRaiz
    simp only [one_mul,suma_fisica_del_tablero]
    rfl
  rw [mesh,sumaSinFiltro,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun e _ => err e)).trans
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,mass]
  apply add_le_add _ (mul_le_mul_of_nonneg_right lost (by positivity))
  have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  calc _ ≤ (n:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n h) (by dsimp [D]; positivity)
       _ = _ := by dsimp [D]; field_simp
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_del_descarte_y_producto
