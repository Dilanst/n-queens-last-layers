import LimitesDeCapasDesdeElPerfilYPrimerOrden
import EstructuraDeLasMedias
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Limites Filter Set
open scoped Topology

theorem niveles_de_una_reparacion {s : ℝ} (primero : CotaDePrimerOrden s) (h : ℕ) (hh : 0<h) :
    ∀ᶠ n : ℕ in atTop,0<count n (n-h) ∧ 0<count n (n-h+1) := by
  filter_upwards [soluciones_eventuales_del_primer_orden primero,eventually_ge_atTop h] with n sol nh
  refine ⟨capa_positiva_si_hay_solucion nh sol,?_⟩
  rw [show n-h+1=n-(h-1) by omega]
  exact capa_positiva_si_hay_solucion (by omega) sol

theorem inversa_con_centro_convergente {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h)
    (w : (n : ℕ)→Cell n→ℝ) {W J : ℝ} (wp : 0≤W) (cap : ∀ n z,|w n z|≤W)
    (center : Tendsto (fun n : ℕ => blancoInverso (h-1) (p ((↑(h-1):ℝ)/n)) (w n) 1/(n:ℝ)^2) atTop (𝓝 J)) :
    (∀ ε>0,Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (w n)) J ε) atTop (𝓝 0)) ∧
    Tendsto (fun n => mediaI n h (w n)) atTop (𝓝 J) := by
  let target := fun n : ℕ => blancoInverso (h-1) (p ((↑(h-1):ℝ)/n)) (w n) 1/(n:ℝ)^2
  have dev (ε : ℝ) (ep : 0<ε) : Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (w n)) J ε) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (inversa_de_la_rama_en_su_malla rama first h hh w W wp cap (ε/2) (half_pos ep))
    · apply Eventually.of_forall; intro n; unfold desviacion
      apply Finset.sum_nonneg; intro _ _; split <;> positivity
    · filter_upwards [Metric.tendsto_nhds.mp center (ε/2) (half_pos ep)] with n close
      unfold desviacion; apply Finset.sum_le_sum; intro Q _
      change (if ε < |Iobs n h (w n) Q-J| then _ else 0)≤(if ε/2 < |Iobs n h (w n) Q-target n| then _ else 0)
      by_cases bad : ε < |Iobs n h (w n) Q-J|
      · have tri:=abs_sub_le (Iobs n h (w n) Q) (target n) J
        rw [Real.dist_eq] at close; change |target n-J|<ε/2 at close
        rw [if_pos bad,if_pos (by linarith only [tri,close,bad])]
      · rw [if_neg bad]; split <;> positivity
  have hi:=media_desde_prob (fun n => n-h+1) (fun n => Iobs n h (w n)) J W
    ((niveles_de_una_reparacion first h hh).mono (fun _ z => z.2))
    ((eventually_ge_atTop h).mono (fun n nh => inversa_acotada n h nh hh (w n) W wp (cap n))) dev
  exact ⟨dev,hi.congr (fun n => (inversa_uniforme n h (w n)).symm)⟩

theorem media_directa_con_centro_convergente {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h)
    (w : (n : ℕ)→Cell n→ℝ) {W J : ℝ} (wp : 0≤W) (cap : ∀ n z,|w n z|≤W)
    (center : Tendsto (fun n : ℕ => blancoInverso (h-1) (p ((↑(h-1):ℝ)/n)) (w n) 1/(n:ℝ)^2) atTop (𝓝 J)) :
    Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 (fraccionDelPerfil b 0*J)) := by
  apply media_directa_desde_inversa h hh.ne' w
    ((niveles_de_una_reparacion first h hh).mono (fun _ H => ⟨H.1.ne',H.2.ne'⟩))
    ((conclusiones_de_capas_fijas rama cont first h).2.1 h hh le_rfl)
  exact (inversa_con_centro_convergente rama first h hh w wp cap center).2
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.niveles_de_una_reparacion
#print axioms ArticuloA.Historias.inversa_con_centro_convergente
#print axioms ArticuloA.Historias.media_directa_con_centro_convergente
