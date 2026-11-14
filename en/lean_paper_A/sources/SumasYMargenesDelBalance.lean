import BalanceFisicoCompleto
open Set
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2
noncomputable section

theorem suma_de_los_grados (n : ℕ) (p : FactoresContinuos) (i : Fin 4) :
    ∑ j : Indice n,gradoInicial n p i j=Wfisico n p := by
  unfold gradoInicial Wfisico
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have eq : ∀ j : Indice n,lines e i=j.val ↔ j=tuplaReal e i :=
    fun j => ⟨fun t => Fin.ext t.symm,fun t => (congrArg Fin.val t).symm⟩
  simp_rw [eq]
  simp

theorem suma_de_las_cargas (n q : ℕ) (p : FactoresContinuos) (i : Fin 4) (w : Wfisico n p≠0) :
    ∑ j : Indice n,cargaLinea n q p i j=(q:ℝ) := by
  simp only [cargaLinea,←Finset.sum_div,←Finset.mul_sum,suma_de_los_grados,mul_div_cancel_right₀ _ w]

theorem suma_de_holguras {n h : ℕ} {p : FactoresContinuos} (hn : 0<n) (i : Fin 4) {C : ℝ}
    (non : 0≤C) (w : Wfisico n p≠0)
    (bal : ∀ j : Indice n,(n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤C) :
    |(∑ j : Indice n,holguraInicial n h p i j)-((2*n-1:ℕ):ℝ)+(↑(n-h):ℝ)|≤2*C := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  let E:=fun j : Indice n => cargaLinea n (n-h) p i j+holguraInicial n h p i j-1
  have eq : (∑ j : Indice n,E j)=(∑ j : Indice n,holguraInicial n h p i j)-((2*n-1:ℕ):ℝ)+(↑(n-h):ℝ) := by
    simp only [E,Finset.sum_sub_distrib,Finset.sum_add_distrib,suma_de_las_cargas _ _ _ _ w]
    simp [Indice,nsmul_eq_mul]; ring
  rw [←eq]
  calc
    _ ≤ ∑ j : Indice n,|E j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Indice n,C/n := Finset.sum_le_sum (fun j _ => (le_div_iff₀ np).mpr (by simpa only [mul_comm] using bal j))
    _ = ((2*n-1:ℕ):ℝ)*(C/n) := by simp [Indice,nsmul_eq_mul]
    _ ≤ (2*(n:ℝ))*(C/n) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg non np.le)
      exact_mod_cast (by omega : 2*n-1≤2*n)
    _ = 2*C := by field_simp; ring

theorem carga_estricta_en_oblicuas {n h : ℕ} {p : FactoresContinuos} {κ M L C : ℝ} (hn : 0<n) (sp : ControlEspacial p κ M L)
    (i : Fin 4) (j : Indice n) (diag : 2 ≤ i.val) (margen : 2*C≤κ*n)
    (bal : (n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤C) :
    cargaLinea n (n-h) p i j≤1-κ/2 := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have d:=oblicuo_admisible n hn j (-1); norm_num at d
  have a:=oblicuo_admisible n hn j 0; norm_num at a
  have lower : κ≤holguraInicial n h p i j := by
    rw [virtual_de_la_malla]
    fin_cases i
    · exact False.elim ((by decide : ¬2 ≤ (0:Fin 4).val) diag)
    · exact False.elim ((by decide : ¬2 ≤ (1:Fin 4).val) diag)
    · exact sp.D.minimo _ d
    · exact sp.A.minimo _ a
  have up:=le_abs_self (cargaLinea n (n-h) p i j+holguraInicial n h p i j-1)
  have small : |cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤κ/2 := by
    calc
      |cargaLinea n (n-h) p i j+holguraInicial n h p i j-1| ≤ C/n :=
        (le_div_iff₀ np).mpr (by simpa only [mul_comm] using bal)
      _ ≤ κ/2 := (div_le_iff₀ np).mpr (by linarith)
  linarith
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_de_holguras
#print axioms ArticuloA.Historias.carga_estricta_en_oblicuas
