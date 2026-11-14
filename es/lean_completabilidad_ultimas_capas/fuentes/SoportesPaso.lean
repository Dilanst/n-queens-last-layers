import FibrasDisponibles
import SaltoPatrones

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte
abbrev Marks := Fin 4 → Bool
open Classical in
noncomputable def occBit {n} (x : State n) (z : Cell n) (m : Marks) (e : Cell n) :=
  decide (occupied x z e m)
open Classical in
noncomputable def avBit {n} (x : State n) (z : Cell n) (m : Marks) (e : Cell n) :=
  decide (availPattern x z e m)

theorem occ_support {n} (x : State n) (ok : Legal x.physical) (z : Cell n) (m : Marks) :
    (board n).countP (occBit x z m) ≤ n := by
  classical
  let xs := (board n).filter (occBit x z m)
  have nd : xs.Nodup := (board_unique n).filter _
  have rows : (xs.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    apply nd.imp_of_mem
    intro e f he hf ne eq
    have a : occupied x z e m := of_decide_eq_true (List.mem_filter.mp he).2
    have b : occupied x z f m := of_decide_eq_true (List.mem_filter.mp hf).2
    exact (legal_pair ok a.1 b.1 ne).1 eq
  have bound := distinct_le _ (List.finRange n) rows (by intro j _; simp [List.finRange,List.mem_ofFn])
  simpa [List.countP_eq_length_filter,xs] using bound

private theorem diffBits (P Q : Prop) [Decidable P] [Decidable Q] [Decidable (¬(Q ↔ P))] :
    (decide P != decide Q) = decide (¬(Q ↔ P)) := by by_cases h : P <;> by_cases g : Q <;> simp [h,g]

def admissible {n} (x : State n) : Choice n → Prop
  | .real c => c ∉ queens x.physical
  | _ => True

theorem step_supports {n} (x : State n) (ok : Legal x.physical) (z : Cell n) (m : Marks)
    (a : Choice n) (ha : admissible x a) :
    (board n).countP (fun e => occBit x z m e != occBit (next x a) z m e) ≤ 5 ∧
    (board n).countP (fun e => avBit x z m e != avBit (next x a) z m e) ≤ 8*n ∧
    (board n).countP (occBit x z m) ≤ n ∧ (board n).countP (avBit x z m) ≤ n*n := by
  classical
  refine ⟨?_,?_,occ_support x ok z m,?_⟩
  · cases a with
    | fail => simp [occBit,occupied,marked,next]
    | real c =>
      simpa only [occBit,diffBits,changed] using real_marks_jump x ok c z ha m
    | virtual e => simpa only [occBit,diffBits,changed] using virtual_marks_jump x ok e z m
  · have eq (a : Choice n) : (fun e => avBit x z m e != avBit (next x a) z m e) =
        fun e => availChanged x (next x a) z e m := by
      funext e
      unfold avBit availChanged
      by_cases p : availPattern x z e m <;> by_cases q : availPattern (next x a) z e m <;> simp [p,q]
    cases a with
    | fail => simp [avBit,availPattern,available,marked,next]
    | real c => rw [eq]; exact real_avail_jump x c z ha m
    | virtual e => rw [eq]; exact virtual_avail_jump x e z m
  · have rows (xs : List (Fin n)) :
        (xs.flatMap (fun r => (List.finRange n).map (fun c => (r,c)))).length = xs.length*n := by
      induction xs with
      | nil => simp
      | cons r xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
    simpa [board,rows] using List.countP_le_length (p := avBit x z m) (l := board n)

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.step_supports
