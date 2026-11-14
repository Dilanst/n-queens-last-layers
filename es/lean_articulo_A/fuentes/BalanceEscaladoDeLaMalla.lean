import PesosYCuotasAntesDelCorte
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
def BalanceMalla (n h : ℕ) (p : FactoresContinuos) (C : ℝ≥0) := ∀ i (j : Indice n),
  (n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤C

theorem presupuesto_absoluto (a b d : ℝ≥0) : within masas a b d ↔ |(a:ℝ)-(b:ℝ)|≤(d:ℝ) := by
  change ((a:ℝ)≤(b:ℝ)+(d:ℝ) ∧ (b:ℝ)≤(a:ℝ)+(d:ℝ)) ↔ _
  rw [abs_le]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem balance_regional {n h p C} (hn : 0<n) (bal : BalanceMalla n h p C)
    (i : Fin 4) (j : Indice n) :
    within masas (probLinea n h p (i,j.val)+(coloresDelPerfil n h p).virtual i j.val) 1 (C/n) := by
  rw [presupuesto_absoluto,NNReal.coe_add,carga_identificada hn]
  change |cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤(C:ℝ)/n
  exact (le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mpr (by simpa only [mul_comm] using bal i j)

theorem offset_regional {n h p C} (hn : 0<n) (w : Wfisico n p≠0) (bal : BalanceMalla n h p C) (i : Fin 4) :
    within masas (famIni n h p i) (cuotaV n h) (2*C/n) := by
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have hl : n-h≤2*n-1 := by omega
  have t:=suma_de_holguras hn i C.property w (bal i)
  rw [presupuesto_absoluto]
  simp only [famIni,cuotaV,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat,
    suma_virtual_inicial,virtualInicial,Nat.cast_sub hl,←sub_div,abs_div,abs_of_pos np]
  exact div_le_div_of_nonneg_right (by convert t using 2; ring) np.le

theorem cap_virtual_fisico {n h p κ m L} (hn : 0<n) (hh : h≤n)
    (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) (m1 : 1≤m) (i : Fin 4) (j : Indice n) :
    (coloresDelPerfil n h p).virtual i j.val≤m := by
  change holguraInicial n h p i j≤(m:ℝ)
  rw [virtual_de_la_malla]
  have x1 : (fraccionHuecos n h:ℝ)≤1 := by
    change (h:ℝ)/(n:ℝ)≤1; exact (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hh)
  have de := oblicuo_admisible n hn j (-1); norm_num at de
  have ae := oblicuo_admisible n hn j 0; norm_num at ae
  fin_cases i <;> simp only [factores,pesosMalla]
  · split_ifs with hj
    · exact (mul_le_of_le_one_left (NNReal.coe_nonneg _) x1).trans (sp.Rmax _ (medio_admisible hj))
    · exact_mod_cast m1
  · split_ifs with hj
    · exact (mul_le_of_le_one_left (NNReal.coe_nonneg _) x1).trans (sp.Cmax _ (medio_admisible hj))
    · exact_mod_cast m1
  · exact sp.Dmax _ de
  · exact sp.Amax _ ae

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.offset_regional
#print axioms ArticuloA.Historias.cap_virtual_fisico
