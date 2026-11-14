import DerivaDirectaEnElProcesoDelArticulo
import ColaFisicaConDerivaFirmada
import ExtremosDeLaReparacionDirecta
import PasosPositivosDeUnaHistoria
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

def pararRaiz {n} (h : ℕ) (p : FactoresContinuos) (u : ℝ≥0) (t : ℕ) (X : State n) :=
  decide (¬(coherent X ∧ X.failed=false ∧ Seguimiento h p X (fraccionAntes n t) u))

def pasoDeRaiz {n} (h T : ℕ) (p : FactoresContinuos) (u : ℝ≥0) :=
  pasoParado (n:=n) (coloresDelPerfil n h p) (freezeAt T (pararRaiz h p u))

theorem presupuesto_de_toda_historia {n h T : ℕ} {p : FactoresContinuos} {κ m ζ C u : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (zp : 0<ζ)
    (tN : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C) (mar : 2*(C:ℝ)≤κ*n)
    (he : u/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (z : Cell n)
    (l : List (ℕ×State n)) (t : ℕ) (x : ℕ×State n) :
    pasosConDeriva (pasoDeRaiz h T p u) (parteDeRaiz p h T z false) (parteDeRaiz p h T z true)
      (constanteDirecta m κ ζ C*(u+1)/n) t x l := by
  induction l generalizing t x with
  | nil => trivial
  | cons y l ih =>
    refine ⟨?_,ih (t+1) y⟩
    rcases x with ⟨j,X⟩
    unfold pasoDeRaiz pasoParado stopped
    by_cases fin : freezeAt T (pararRaiz h p u) j X=true
    · rw [if_pos fin,avg_point,avg_point,add_comm]
      exact ⟨le_add_of_nonneg_right (zero_le _),le_add_of_nonneg_right (zero_le _)⟩
    · have go : freezeAt T (pararRaiz h p u) j X=false := Bool.eq_false_of_not_eq_true fin
      obtain ⟨jt,openState⟩:=(Bool.or_eq_false_iff.mp go)
      have jt' : j<T := by simpa [decide_eq_false_iff_not] using jt
      have ok : coherent X ∧ X.failed=false ∧ Seguimiento h p X (fraccionAntes n j) u := by simpa [pararRaiz] using openState
      rw [if_neg fin,avg_push,avg_push]
      exact deriva_directa_con_el_perfil hn hh sp kp m1 zp jt' tN floor bal mar he ho X ok.2.2 ok.1 ok.2.1 z

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.presupuesto_de_toda_historia
