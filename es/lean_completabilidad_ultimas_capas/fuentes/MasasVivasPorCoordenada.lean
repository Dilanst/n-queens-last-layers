import TransicionAntesDeLaPrimeraSalida
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

theorem masa_viva_acotada {n p κ m L} (X : State n) (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) :
    masaN p X≤(n:ℝ≥0)^2*m^4 := by
  change (masaN p X:ℝ)≤(↑((n:ℝ≥0)^2*m^4):ℝ)
  rw [masa_del_estado]
  have one (e : Cell n) : (if E2.available X (lines e) then pesoFisico n p e else 0)≤(m:ℝ)^4 := by
    split_ifs with on
    · rw [←peso_para_el_nucleo p e]; exact_mod_cast cota_de_un_peso sp e
    · positivity
  calc masaActiva p X ≤ ∑ _e : Cell n,(m:ℝ)^4 := Finset.sum_le_sum (fun e _ => one e)
       _ = _ := by simp [Cell,pow_two,nsmul_eq_mul]

theorem masa_virtual_acotada {n h p κ m L} (hn : 0<n) (hh : h≤n)
    (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) (m1 : 1≤m) (X : State n) (i : Fin 4) :
    familiaN p h X i≤(n:ℝ≥0)*(2*m) := by
  change (familiaN p h X i:ℝ)≤(↑((n:ℝ≥0)*(2*m)):ℝ)
  rw [suma_virtual_del_estado]
  have one (j : Indice n) : (if X.active i j.val then holguraInicial n h p i j else 0)≤(m:ℝ) := by
    split_ifs
    · exact cap_virtual_fisico hn hh sp m1 i j
    · exact m.property
  calc virtualActiva h p X i ≤ ∑ _j : Indice n,(m:ℝ) := Finset.sum_le_sum (fun j _ => one j)
       _ = ((2*n-1:ℕ):ℝ)*m := by simp [Indice,nsmul_eq_mul]
       _ ≤ (2*(n:ℝ))*m := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2*n-1≤2*n)) m.property
       _ = _ := by push_cast; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_viva_acotada
#print axioms ArticuloA.Historias.masa_virtual_acotada
