import HistoriasLegales

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

private theorem diag_pair {n} (u y : Cell n) : diagonalOK u y ↔
    (lines u 2 ≠ lines y 2 ∧ lines u 3 ≠ lines y 3) := by
  simp only [diagonalOK,lines]
  omega

theorem unmarked_eq_candidate {n} (x : State n) (z e : Cell n) :
    occupied x z e (fun _ => false) ↔ Candidate x.physical z e := by
  have eq : marked x z e (fun _ => false) ↔ freeDiagonals x.physical (corners (z,e)).1 ∧
      freeDiagonals x.physical (corners (z,e)).2 := by
    constructor
    · intro h; constructor <;> intro u hu <;> apply (diag_pair _ _).mpr
      · exact ⟨h 0 u hu,h 1 u hu⟩
      · exact ⟨h 2 u hu,h 3 u hu⟩
    · rintro ⟨a,b⟩ j
      have jj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases jj with rfl|rfl|rfl|rfl <;> intro u hu
      · exact ((diag_pair _ _).mp (a _ hu)).1
      · exact ((diag_pair _ _).mp (a _ hu)).2
      · exact ((diag_pair _ _).mp (b _ hu)).1
      · exact ((diag_pair _ _).mp (b _ hu)).2
  simp only [occupied,Candidate,eq]

theorem unmarked_count {n} (x : State n) (z : Cell n) :
    (board n).countP (occBit x z (fun _ => false)) = physicalCount x.physical z := by
  classical
  have aux (es : List (Cell n)) : es.countP (occBit x z (fun _ => false)) =
      counting.over es (fun e => indicator (Candidate x.physical z e)) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      rw [List.countP_cons,ih]
      change _ = indicator (Candidate x.physical z e) + counting.over es _
      by_cases h : Candidate x.physical z e <;> simp [occBit,unmarked_eq_candidate,indicator,h,Nat.add_comm]
  exact aux _

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.unmarked_count
