import PerdidaDeParesInversos
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

open Classical in
noncomputable def eligiblePair {n} (p : Placement n) (e f : Cell n) :=
  decide (e ≠ f ∧ freeDiagonals p (corners (e,f)).2)
def pairSum {n} (xs ys : List (Cell n)) (test : Cell n → Cell n → Bool) :=
  (xs.map (fun e => ys.countP (test e))).sum

theorem old_lost {n} (p : Placement n) (ok : Legal p) (g : Cell n) :
    pairSum (queens p) (queens p) (fun e f => eligiblePair p e f && !eligiblePair (toggle g p) e f) ≤ 2*n := by
  classical
  have row (e) : (queens p).countP (fun f => eligiblePair p e f && !eligiblePair (toggle g p) e f) ≤
      (queens p).countP (fun f => hitInverse g e f true || hitInverse g e f false) := by
    apply List.countP_mono_left; intro f _ hv
    simp [eligiblePair] at hv
    exact lost_hits p g e f hv.1.2 (hv.2.resolve_left hv.1.1)
  have part (L : List (Cell n)) : pairSum L (queens p) (fun e f =>
      eligiblePair p e f && !eligiblePair (toggle g p) e f) ≤ hitCount p g L := by
    induction L with
    | nil => exact Nat.le_refl 0
    | cons e es ih => exact Nat.add_le_add (row e) ih
  exact Nat.le_trans (part _) (hits_old_pairs p ok g)

/-- The cross weights of newly formed ordered pairs can have either order.
The diagonal (g,g) is excluded. -/
theorem new_pairs {n} (p : Placement n) (ok : Legal p) (g : Cell n) (test : Cell n → Cell n → Bool)
    (distinct : test g g = false) :
    pairSum (g::queens p) (g::queens p) test ≤ pairSum (queens p) (queens p) test + 2*n := by
  let L := queens p
  have col (xs : List (Cell n)) :
      pairSum xs (g::L) test ≤ pairSum xs L test + xs.length := by
    induction xs with
    | nil => exact Nat.le_refl 0
    | cons x xs ih =>
      change (g::L).countP (test x) + pairSum xs (g::L) test ≤ L.countP (test x) + pairSum xs L test + _
      rw [List.countP_cons]; cases hx : test x g <;> simp [hx] <;> omega
  have r := List.countP_le_length (p:=test g) (l:=L)
  have len := distinct_le _ (List.finRange n) (distinctRows ok) (by
    intro j _; simp [List.finRange,List.mem_ofFn])
  simp only [List.length_map,List.length_finRange] at len
  change (g::L).countP (test g) + pairSum L (g::L) test ≤ _
  rw [List.countP_cons]; simp only [distinct, Bool.false_eq_true, if_false, Nat.add_zero]
  have c := col L
  change L.length ≤ n at len
  change L.countP (test g) + pairSum L (g :: L) test ≤ pairSum L L test + 2*n
  omega
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.old_lost
#print axioms ArticuloA.Trayectoria.E2.new_pairs
