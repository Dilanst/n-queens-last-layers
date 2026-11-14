import ExcepcionesDelRevelado
import DescomposicionInversa
import ErrorDelGeneradorPorRaiz
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair Adjunto

theorem separadas {n} (e f : Cell n) : compatible e f ↔ ∀ i, lines e i ≠ lines f i := by
  constructor
  · rintro ⟨r,c,d,a⟩ i
    have hr : e.1.val ≠ f.1.val := fun eq => r (Fin.ext eq)
    have hc : e.2.val ≠ f.2.val := fun eq => c (Fin.ext eq)
    have fin : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases fin with rfl|rfl|rfl|rfl <;> simp [lines] <;> omega
  · intro H
    have r := H 0; have c := H 1; have d := H 2; have a := H 3
    simp [lines] at r c d a
    exact ⟨fun eq => r (congrArg Fin.val eq),fun eq => c (congrArg Fin.val eq),by omega,a⟩

/-- Neither birth can kill either diagonal of the proposed inverse insertion. -/
theorem dos_destinos {n} (e f : Cell n) (ok : compatible e f) (j : Fin 4) (diag : 2 ≤ j) :
    lines (corners (e,f)).2 j ≠ lines e j ∧ lines (corners (e,f)).2 j ≠ lines f j := by
  have r : e.1.val ≠ f.1.val := fun eq => ok.1 (Fin.ext eq)
  have c : e.2.val ≠ f.2.val := fun eq => ok.2.1 (Fin.ext eq)
  have fin : j=2 ∨ j=3 := by omega
  rcases fin with rfl|rfl <;> simp [lines,corners] <;> omega

open Classical in
noncomputable def malPar {n} (m : Mark n) : Bool := decide (¬ compatible m.1 m.2)

/-- The O(n^3) exclusions in the inverse quadrature, with an explicit constant. -/
theorem pares_excluidos (n : Nat) :
    (grid (board n) (board n)).countP malPar ≤ 4*n^3 := by
  classical
  have per (e : Cell n) : (board n).countP (fun f => malPar (e,f)) ≤ 4*n := by
    apply Nat.le_trans _ (by simpa using excepciones_reales n [] (lines e))
    apply List.countP_mono_left; intro f _ h
    simp only [malPar,decide_eq_true_eq,separadas] at h
    simp only [exceptional,List.any_nil,Bool.or_false]
    apply List.any_eq_true.mpr
    obtain ⟨j,eq⟩ := Classical.not_forall.mp h
    exact ⟨j,by simp [List.finRange,List.mem_ofFn] <;> omega,beq_iff_eq.mpr (Classical.not_not.mp eq).symm⟩
  have bound (l : List (Cell n)) : (grid l (board n)).countP malPar ≤ l.length*(4*n) := by
    induction l with
    | nil => simp [grid]
    | cons e es ih =>
      change ((List.map (fun f => (e,f)) (board n)) ++ grid es (board n)).countP malPar ≤ _
      rw [List.countP_append,List.countP_map,List.length_cons,Nat.succ_mul,Nat.add_comm (es.length*_)]
      exact Nat.add_le_add (per _) ih
  have h := bound (board n)
  rw [board_card] at h
  calc _ ≤ _ := h
       _ = _ := by simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]; ac_rfl
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.dos_destinos
#print axioms ArticuloA.Trayectoria.E2.pares_excluidos
