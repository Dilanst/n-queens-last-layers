import IntegrandoDeLaReparacionDirecta
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

def holgurasFisicas {n} (p : FactoresContinuos) (z e : Cell n) :=
  factoresDelCruce p (medio n z.1.val) (medio n z.2.val) (medio n e.1.val) (medio n e.2.val)

theorem destino_en_su_centro {n h} (p : FactoresContinuos) (z e : Cell n) (j : Fin 4) :
    (holguraInicial n h p (side j) ⟨key z e j,on_board (dest z e j) (side j)⟩:ℝ)=holgurasFisicas p z e j := by
  rw [virtual_de_la_malla]
  have row:=nodos_de_una_casilla (z.1,e.2)
  have col:=nodos_de_una_casilla (e.1,z.2)
  fin_cases j
  · change (p.diagonal _ : ℝ)=(p.diagonal _ : ℝ)
    exact congrArg (fun t => (p.diagonal t:ℝ)) row.1
  · change (p.anti _ : ℝ)=(p.anti _ : ℝ)
    exact congrArg (fun t => (p.anti t:ℝ)) row.2
  · change (p.diagonal _ : ℝ)=(p.diagonal _ : ℝ)
    exact congrArg (fun t => (p.diagonal t:ℝ)) col.1
  · change (p.anti _ : ℝ)=(p.anti _ : ℝ)
    exact congrArg (fun t => (p.anti t:ℝ)) col.2

theorem diferencia_en_el_destino {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z e : Cell n) (j : Fin 4) :
    |((1-cargaDeDestino h p z e j:ℝ≥0):ℝ)-holgurasFisicas p z e j|≤(C:ℝ)/n := by
  let i:=side j
  let v : Indice n:=⟨key z e j,on_board (dest z e j) (side j)⟩
  have cap:=(cargas_para_un_cruce hn sp kp bal margen z).1 e j
  rw [NNReal.coe_sub cap,NNReal.coe_one,←destino_en_su_centro (h:=h)]
  change |1-(probLinea n h p (i,v.val):ℝ)-(holguraInicial n h p i v:ℝ)|≤_
  rw [carga_identificada (by omega : 0<n)]
  rw [show 1-cargaLinea n (n-h) p i v-holguraInicial n h p i v=
      -(cargaLinea n (n-h) p i v+holguraInicial n h p i v-1) by ring,abs_neg]
  exact (le_div_iff₀ (by exact_mod_cast (by omega : 0<n) : 0<(n:ℝ))).mpr
    (by simpa only [mul_comm] using bal i v)

def holguraDeLaMalla {n} (h : ℕ) (p : FactoresContinuos) (z e : Cell n) :=
  masas.four (fun j => 1-cargaDeDestino h p z e j)

theorem diferencia_del_producto {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (bal : BalanceMalla n h p C)
    (margen : 2*(C:ℝ)≤κ*n) (z e : Cell n) :
    |(holguraDeLaMalla h p z e:ℝ)-
      factorDelCruce p (medio n z.1.val) (medio n z.2.val) (medio n e.1.val) (medio n e.2.val)|≤
        4*(m:ℝ)^3*((C:ℝ)/n) := by
  let u:=fun j => ((1-cargaDeDestino h p z e j:ℝ≥0):ℝ)
  have cap (j : Fin 4) : |u j|≤m := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast ((tsub_le_self : (1:ℝ≥0)-cargaDeDestino h p z e j≤1).trans m1)
  have vcap:=rango_de_holguras sp (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
    (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
  have est:=cuatro_factores u (holgurasFisicas p z e) m _ cap vcap
    (diferencia_en_el_destino hn sp kp bal margen z e)
  change |(u 0*u 1)*(u 2*u 3)-_|≤_
  rwa [←mul_assoc (u 0*u 1) (u 2) (u 3)]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.diferencia_del_producto
