import DelTerminalE2AlUniforme
import TodosLosCrucesAlFinalDeE2
import BandaDelValorDelOptimo
open Filter
open scoped NNReal BigOperators Topology
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Corte Repair Limites
noncomputable section
open Classical

def blancoNormalizado {n} (h : ℕ) (p : FactoresContinuos) (z : Cell n) : ℝ :=
  (blancoFinalDeMalla h p z:ℝ)/n

theorem mala_uniforme_del_blanco_finito (h : ℕ→ℕ) (p : ℕ→FactoresContinuos) (d : ℕ→ℝ)
    (κ m C : ℝ≥0) (kp : 0<κ) (m1 : 1≤m) (L : ℝ) (η : ℝ) (ep : 0<η)
    (small : Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0))
    (data : ∀ᶠ n : ℕ in atTop,h n≤n ∧ 0<count n (n-h n) ∧ ControlEspacial (p n) κ m L ∧
       BalanceMalla n (h n) (p n) C ∧ Tres n (h n) (coloresDelPerfil n (h n) (p n)) (d n)) :
    Tendsto (fun n => probCruceMalo n (h n) (blancoNormalizado (h n) (p n)) η) atTop (𝓝 0) := by
  let ε:ℝ≥0:=⟨η,ep.le⟩
  obtain ⟨c,cp,N₁,concentration⟩:=todos_los_cruces_al_final_de_E2 κ m C ε kp m1 (by exact_mod_cast ep)
  refine Entropia.transferencia _ d cp ?_ small ?_
  · apply Eventually.of_forall; intro n; unfold probCruceMalo
    apply Finset.sum_nonneg; intro _ _; split <;> positivity
  · filter_upwards [data,eventually_ge_atTop N₁,eventually_gt_atTop 0] with n nd ng np
    obtain ⟨hh,counted,sp,bal,l1⟩:=nd
    let u:=coloresDelPerfil n (h n) (p n)
    let a:=blancoNormalizado (n:=n) (h n) (p n)
    let F:=fun (x : State n) => ∃ z,(ε:ℝ)*n≤|(physicalCount x.physical z:ℝ)-a z*n|
    have same (z : Cell n) : a z*n=(blancoFinalDeMalla (h n) (p n) z:ℝ) :=
      div_mul_cancel₀ _ (by exact_mod_cast np.ne')
    have est:=concentration n ng _ hh _ L sp bal
    have tail : (avg masas (terminalE2 n (h n) u) (mark masas F)).val≤Real.exp (-(c*n)) := by
      let S:=kernel (n:=n) masas u (·⁻¹)
      let N:=2*n-1
      let X:=initial n (h n)
      let B (x : State n) := ∃ z,(ε:ℝ)*n≤|(physicalCount x.physical z:ℝ)-(blancoFinalDeMalla (h n) (p n) z:ℝ)|
      have eqF : F=B := by
        funext x
        apply propext
        constructor <;> rintro ⟨z,hz⟩ <;> refine ⟨z,?_⟩
        · rwa [←same]
        · rwa [same]
      rw [eqF]
      have project:=proyectar_ultimo_estado S 0 N X (mark masas B)
      exact (congrArg NNReal.toReal project.symm).le.trans est
    exact transferencia_a_cruces_vacios np counted (p n) sp (NNReal.coe_pos.mpr kp) (d n) (c*n) η a l1 tail

/-- A varying hole count is admitted within the fixed entropy band. The first-order
count and regularity of the continuum profile are used through the interface of the entropy comparison. -/
theorem directa_de_la_rama {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (K : ℕ)
    (ext : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0)))
    (h : ℕ→ℕ) (hk : ∀ᶠ n : ℕ in atTop,h n≤K) (C : ℝ≥0)
    (bal : ∀ᶠ n : ℕ in atTop,BalanceMalla n (h n) (p ((h n:ℝ)/n)) C)
    (η : ℝ) (ep : 0<η) :
    Tendsto (fun n => probCruceMalo n (h n) (blancoNormalizado (h n) (p ((h n:ℝ)/n))) η) atTop (𝓝 0) := by
  obtain ⟨d,small,cost⟩:=L1_de_la_rama_y_el_conteo rama K ext
  have zero : (0:ℝ)∈Set.Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 zero
  have ext0:=ext (admisibilidad_del_lleno full)
  rw [normalizacion_de_simkin full (rama.espacio 0 zero) rama.kp rama.lp] at ext0
  have sol:=soluciones_eventuales_del_primer_orden (conteo_local_implica_primer_orden ext0)
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  apply mala_uniforme_del_blanco_finito _ _ d lo hi C (by exact_mod_cast rama.kp)
    (by exact_mod_cast rama.m1) L η ep small
  filter_upwards [hk,bal,cost,sol,eventually_ge_atTop (2*K),eventually_gt_atTop 0] with n bound mesh kl s big np
  have hh : 2*h n≤n := by omega
  have half : (h n:ℝ)/n≤1/2 := by
    apply (div_le_iff₀ (by exact_mod_cast np : 0<(n:ℝ))).mpr
    have cut : 2*(h n:ℝ)≤n := by exact_mod_cast hh
    linarith
  exact ⟨by omega,capa_positiva_si_hay_solucion (by omega) s,rama.espacio _ ⟨by positivity,half⟩,mesh,kl (h n) bound⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.directa_de_la_rama
