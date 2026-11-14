import MasaDeLosTablerosSeleccionados
import SoporteUniformeDeLaLeyExitosa
import TransferenciaAsintotica
import DelEventoPorCrucesAlLimite
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel Trayectoria.E2 RealFinita Corte Repair Limites
noncomputable section
open Classical

theorem transferencia_finita_del_terminal {n h} (hn : 0<n) (cnt : 0<count n (n-h))
    (p : FactoresContinuos) {κ m L : ℝ} (sp : ControlEspacial p κ m L) (kp : 0<κ)
    (d r : ℝ) (l1 : Tres n h (coloresDelPerfil n h p) d) (bad : Tablero n (n-h)→Prop)
    (F : State n→Prop) (incl : ∀ x,esExito x → ∀ b : Tablero n (n-h),bad b → x.physical=b.val → F x)
    (rare : (avg masas (terminalE2 n h (coloresDelPerfil n h p)) (mark masas F)).val≤Real.exp (-r)) :
    (∑ b : Tablero n (n-h),if bad b then (count n (n-h):ℝ)⁻¹ else 0)*(r-d)≤d+Real.log 2 := by
  let u:=coloresDelPerfil n h p
  let s:=exitoE2 n h u
  let prob:=fun b : Tablero n (n-h) => masaTablero b h u/s
  have norm : ∑ _ : Tablero n (n-h),(count n (n-h):ℝ)⁻¹=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,cardinal_nivel,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast cnt.ne')
  have spos : 0<s := (Real.exp_pos (-d)).trans_le l1.2.1
  have support (b : Tablero n (n-h)) : 0<prob b := div_pos (masa_positiva_en_cada_tablero hn p sp kp b) spos
  have sub : ∑ b,prob b≤1 := by
    have total:=suma_de_masas_condicionables (n:=n) (q:=n-h) (h:=h) u (fun _ => True) esExito (fun _ h _ _ _ => h)
    simp only [if_true] at total
    change (∑ b : Tablero n (n-h),masaTablero b h u)≤s at total
    change (∑ b : Tablero n (n-h),masaTablero b h u/s)≤1
    rw [←Finset.sum_div]; exact (div_le_one spos).mpr total
  have joint:=(suma_de_masas_condicionables u bad F incl).trans rare
  let B:=fun b => decide (bad b)
  have eq : (∑ b : Tablero n (n-h),if B b then prob b else 0)=
      (∑ b : Tablero n (n-h),if bad b then masaTablero b h u else 0)/s := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro b _
    by_cases test : bad b <;> simp [B,prob,test]
  have est:=Entropia.exito_y_cola spos eq joint l1.2.1
  have bin:=Entropia.coste_binario Finset.univ (fun _ : Tablero n (n-h) => (count n (n-h):ℝ)⁻¹) prob B (r-d)
    (fun _ _ => inv_pos.mpr (by exact_mod_cast cnt)) (fun b _ => support b) norm sub est
  change (∑ b,if B b then (count n (n-h):ℝ)⁻¹ else 0)*(r-d)≤KLcondicionado n (n-h) h u+Real.log 2 at bin
  simpa only [B,decide_eq_true_eq] using bin.trans (add_le_add_right l1.2.2 _)

theorem transferencia_a_cruces_vacios {n h} (hn : 0<n) (cnt : 0<count n (n-h))
    (p : FactoresContinuos) {κ m L : ℝ} (sp : ControlEspacial p κ m L) (kp : 0<κ)
    (d r η : ℝ) (a : Cell n→ℝ) (l1 : Tres n h (coloresDelPerfil n h p) d)
    (rare : (avg masas (terminalE2 n h (coloresDelPerfil n h p)) (mark masas (fun x =>
      ∃ z, η*(n:ℝ) ≤ |(physicalCount x.physical z:ℝ)-a z*n|))).val≤Real.exp (-r)) :
    probCruceMalo n h a η*(r-d)≤d+Real.log 2 := by
  let B (b : Tablero n (n-h)) := ∃ z∈cruces b.val,η < |(crossDegree (n-h) b.val z:ℝ)/n-a z|
  have tail:=transferencia_finita_del_terminal hn cnt p sp kp d r l1 B (fun x => ∃ z, η*(n:ℝ) ≤ |(physicalCount x.physical z:ℝ)-a z*n|) (by
    intro X _ b bad eq
    obtain ⟨z,mem,hz⟩:=bad
    refine ⟨z,?_⟩
    rw [eq,physical_eq_crossDegree b.val z (legal_y_tamano b).1 ((Finset.mem_filter.mp mem).2),(legal_y_tamano b).2]
    have np : 0<(n:ℝ) := by exact_mod_cast hn
    have scale:=mul_le_mul_of_nonneg_right hz.le np.le
    apply scale.trans_eq
    calc |(crossDegree (n-h) b.val z:ℝ)/n-a z| * n =
          |((crossDegree (n-h) b.val z:ℝ)/n-a z)*n| := by rw [abs_mul,abs_of_nonneg np.le]
         _ = _ := by rw [sub_mul,div_mul_cancel₀ _ np.ne']) rare
  unfold probCruceMalo
  rw [←Finset.sum_attach,Finset.attach_eq_univ]
  classical
  convert tail using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : B x
  · simp only [if_pos hx,if_pos (show ∃ z∈cruces x.val,η < |(crossDegree (n-h) x.val z:ℝ)/n-a z| from hx)]
  · simp only [if_neg hx,if_neg (show ¬∃ z∈cruces x.val,η < |(crossDegree (n-h) x.val z:ℝ)/n-a z| from hx)] 

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.transferencia_a_cruces_vacios
