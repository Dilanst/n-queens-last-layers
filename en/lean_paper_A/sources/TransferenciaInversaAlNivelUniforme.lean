import ConcentracionInversaAlFinalDeE2
import DelTerminalE2AlUniforme
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Limites Filter
open scoped Topology
theorem inversa_uniforme_al_blanco_discreto (h : ℕ) (hh : 0<h) (p : ℕ→FactoresContinuos)
    (d : ℕ→ℝ) (κ m C : ℝ≥0) (kp : 0<κ) (m1 : 1≤m) (L W η : ℝ) (wp : 0≤W) (ep : 0<η)
    (w : (n : ℕ)→Cell n→ℝ) (cap : ∀ n e,|w n e|≤W)
    (small : Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0))
    (data : ∀ᶠ n : ℕ in atTop,0<count n (n-(h-1)) ∧ ControlEspacial (p n) κ m L ∧
       BalanceMalla n (h-1) (p n) C ∧ Tres n (h-1) (coloresDelPerfil n (h-1) (p n)) (d n)) :
    Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (w n)) (blancoInverso (h-1) (p n) (w n) 1/(n:ℝ)^2) η)
      atTop (𝓝 0) := by
  let ε:ℝ≥0:=⟨η,ep.le⟩
  obtain ⟨c,cp,N₁,tail⟩:=concentracion_inversa_de_E2_completo κ m C ε W wp kp m1 (show 0<ε from ep)
  obtain ⟨N₂,large⟩:=exists_nat_gt (4/c)
  refine Entropia.transferencia _ d (half_pos cp) ?_ small ?_
  · apply Eventually.of_forall; intro n; unfold desviacion
    apply Finset.sum_nonneg; intro _ _; split <;> positivity
  · filter_upwards [data,eventually_ge_atTop N₁,eventually_ge_atTop N₂,eventually_ge_atTop h] with n nd ng nb nh
    obtain ⟨ct,sp,bal,l1⟩:=nd
    have same : n-(h-1)=n-h+1 := by omega
    let u:=coloresDelPerfil n (h-1) (p n)
    let B:=blancoInverso (h-1) (p n) (w n) 1
    let F:=fun (x : State n) => η*(n:ℝ)^2≤|inversasDelTablero x.physical (w n)-B|
    have est:=tail n ng (h-1) (by omega) (p n) L sp bal (w n) (cap n)
    have proj:=proyectar_ultimo_estado (kernel (n:=n) masas u (·⁻¹)) 0 (2*n-1) (initial n (h-1)) (mark masas F)
    have r : 4/c≤(n:ℝ) := large.le.trans (by exact_mod_cast nb)
    have c2 : (2:ℝ)≤c/2*n := by linarith only [(div_le_iff₀ cp).mp r]
    have ex : 3≤Real.exp (c/2*n) := by linarith only [Real.add_one_le_exp (c/2*n),c2]
    have penalty : 3*Real.exp (-(c*n))≤Real.exp (-(c/2*n)) := by
      calc _ ≤ Real.exp (c/2*n)*Real.exp (-(c*n)) := mul_le_mul_of_nonneg_right ex (Real.exp_nonneg _)
           _ = _ := by rw [←Real.exp_add]; congr 1; ring
    have rare : (avg masas (terminalE2 n (h-1) u) (mark masas F)).val≤Real.exp (-(c/2*n)) :=
      (congrArg NNReal.toReal proj.symm).le.trans (est.trans penalty)
    let bad:=fun Q : Tablero n (n-(h-1)) => η < |Iobs n h (w n) Q.val-B/(n:ℝ)^2|
    have np : 0<n := by omega
    have incl (x) (_ : esExito x) (Q : Tablero n (n-(h-1))) (hit : bad Q) (eq : x.physical=Q.val) : F x := by
      have legal:=(legal_y_tamano Q).1
      have size:=(legal_y_tamano Q).2.trans same
      have norm : Iobs n h (w n) Q.val=inversasDelTablero Q.val (w n)/(n:ℝ)^2 := by
        rw [←conteo_en_el_nivel_inverso Q.val (w n) size legal]; rfl
      change η < |Iobs n h (w n) Q.val-B/(n:ℝ)^2| at hit
      rw [norm,←sub_div,abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))] at hit
      change η*(n:ℝ)^2≤|inversasDelTablero x.physical (w n)-B|
      rw [eq]; exact ((lt_div_iff₀ (pow_pos (by exact_mod_cast np : 0<(n:ℝ)) 2)).mp hit).le
    have applied:=transferencia_finita_del_terminal np ct (p n) sp (NNReal.coe_pos.mpr kp) (d n) (c/2*n) l1 bad F incl rare
    unfold desviacion; rw [←same,←Finset.sum_attach,Finset.attach_eq_univ]
    exact applied
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.inversa_uniforme_al_blanco_discreto
