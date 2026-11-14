import Interpretacion
import Std.Internal.Rat

namespace ArticuloA

theorem queenLength {n xs} (b : @Mask (Cell n) xs) :
    (queens b).length = pieces b := by
  induction b <;> simp_all [queens, pieces]

theorem distinctRows {n xs} {b : @Mask (Cell n) xs} (h : Legal b) :
    ((queens b).map Prod.fst).Nodup :=
  List.pairwise_map.mpr (h.imp (fun e => e.1))

theorem distinctColumns {n xs} {b : @Mask (Cell n) xs} (h : Legal b) :
    ((queens b).map Prod.snd).Nodup :=
  List.pairwise_map.mpr (h.imp (fun e => e.2.1))

private theorem complementPerm {α : Type} [DecidableEq α] (used pool : List α)
    (d : used.Nodup) (sub : ∀ a ∈ used, a ∈ pool) :
    ∃ free, pool.Perm (used ++ free) := by
  induction used generalizing pool with
  | nil => exact ⟨pool, .refl _⟩
  | cons a rest ih =>
    have ha := sub a (by simp)
    obtain ⟨missing, tail⟩ := List.nodup_cons.mp d
    obtain ⟨free, perm⟩ := ih (pool.erase a) tail (by
      intro b hb
      have ne : b ≠ a := fun e => missing (e ▸ hb)
      exact (List.mem_erase_of_ne ne).mpr (sub b (by simp [hb])))
    exact ⟨free, (List.perm_cons_erase ha).trans (perm.cons a)⟩

private theorem finRangeNodup (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj lt eq
  have val := congrArg Fin.val eq
  simp only [List.getElem_finRange] at val
  exact (Nat.ne_of_lt lt) val

/-- The complement consists of n minus the number of distinct used indices. -/
theorem freeIndices {n : Nat} (used : List (Fin n)) (d : used.Nodup) :
    ∃ free : List (Fin n), free.Nodup ∧ free.length = n-used.length ∧
      ∀ i, i ∈ free ↔ i ∉ used := by
  have allMem (i : Fin n) : i ∈ List.finRange n := by
    simp [List.finRange, List.mem_ofFn]
  obtain ⟨free, perm⟩ := complementPerm used (List.finRange n) d (fun i _ => allMem i)
  have nd := perm.nodup (finRangeNodup n)
  obtain ⟨_, df, disj⟩ := List.pairwise_append.mp nd
  have len := perm.length_eq
  simp only [List.length_finRange, List.length_append] at len
  refine ⟨free, df, by omega, ?_⟩
  intro i
  constructor
  · intro hf hu
    exact disj i hu i hf rfl
  · intro hu
    exact (List.mem_append.mp (perm.mem_iff.mp (allMem i))).resolve_left hu

private theorem lastIndex {n : Nat} (hn : 1 ≤ n) (used : List (Fin n))
    (d : used.Nodup) (len : used.length = n-1) :
    ∃ i, ∀ j, j ∉ used ↔ j = i := by
  obtain ⟨free, _, size, mem⟩ := freeIndices used d
  have one : free.length = 1 := by omega
  obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp one
  exact ⟨i, fun j => by rw [← mem, hi]; simp⟩

theorem uniqueEmptyCross {n xs} (hn : 1 ≤ n) {b : @Mask (Cell n) xs}
    (legal : Legal b) (size : pieces b = n-1) :
    ∃ z : Cell n, ∀ c : Cell n,
      (c.1 ∉ (queens b).map Prod.fst ∧ c.2 ∉ (queens b).map Prod.snd) ↔ c = z := by
  obtain ⟨r, hr⟩ := lastIndex hn _ (distinctRows legal) (by simp [queenLength, size])
  obtain ⟨s, hs⟩ := lastIndex hn _ (distinctColumns legal) (by simp [queenLength, size])
  exact ⟨(r,s), fun c => by rw [hr, hs]; cases c; simp⟩

/-- Squares supporting a one-bit insertion accepted by test, in board order. -/
def destinations {α : Type} {xs : List α} (b : Mask xs) (test : Mask xs → Bool) : List α :=
  match b with
  | .empty => []
  | .skip (x := x) t =>
    let tail := destinations t (fun u => test (.skip u))
    if test (.take t) then x :: tail else tail
  | .take t => destinations t (fun u => test (.take u))

theorem destinationSublist {α xs} (b : @Mask α xs) (test : Mask xs → Bool) :
    (destinations b test).Sublist xs := by
  induction b with
  | empty => exact .slnil
  | skip t ih => simp only [destinations]; split
                 · exact .cons₂ _ (ih _)
                 · exact .cons _ (ih _)
  | take t ih => exact .cons _ (ih _)

theorem destinationLength {α xs} (b : @Mask α xs) (test : Mask xs → Bool) :
    (destinations b test).length = addSum b (fun u => if test u then 1 else 0) := by
  induction b with
  | empty => rfl
  | skip t ih =>
    simp only [destinations, addSum]
    split <;> simp_all [Nat.add_comm]
  | take t ih => exact ih _

theorem insertionWitness {n xs} (b : @Mask (Cell n) xs) (test : Mask xs → Bool)
    (c : Cell n) (mem : c ∈ destinations b test) :
    ∃ u, Adds b u ∧ test u = true ∧ (queens u).Perm (c :: queens b) := by
  induction b with
  | empty => simp [destinations] at mem
  | skip t ih =>
    simp only [destinations] at mem
    by_cases next : test (.take t) = true
    · rw [if_pos next] at mem
      rcases List.mem_cons.mp mem with eq | mem
      · subst c; exact ⟨_, .here t, next, .refl _⟩
      · obtain ⟨u, step, ok, perm⟩ := ih _ mem
        exact ⟨_, .skip step, ok, perm⟩
    · rw [if_neg next] at mem
      obtain ⟨u, step, ok, perm⟩ := ih _ mem
      exact ⟨_, .skip step, ok, perm⟩
  | take t ih =>
    obtain ⟨u, step, ok, perm⟩ := ih _ mem
    exact ⟨_, .take step, ok, (perm.cons _).trans (.swap _ _ _)⟩

private theorem destExists {α xs} {b u : @Mask α xs} (step : Adds b u)
    (test : Mask xs → Bool) (ok : test u = true) :
    ∃ c, c ∈ destinations b test := by
  induction step with
  | here => simp [destinations, ok]
  | skip _ ih =>
    obtain ⟨c, hc⟩ := ih (fun v => test (.skip v)) ok
    exact ⟨c, by simp only [destinations]; split <;> simp_all⟩
  | take _ ih => exact ih (fun v => test (.take v)) ok

/-- A legal full placement obtained by adding one queen to b. -/
def Completable {n : Nat} (b : Mask (board n)) : Prop :=
  ∃ u, Adds b u ∧ Legal u ∧ pieces u = n

private theorem singleList {α : Type} (cs : List α) (z : α) (nd : cs.Nodup)
    (all : ∀ c ∈ cs, c = z) : cs = [] ∨ cs = [z] := by
  cases cs with
  | nil => exact Or.inl rfl
  | cons c cs =>
    have cz := all c (by simp)
    subst c
    cases cs with
    | nil => exact Or.inr rfl
    | cons d ds =>
      have dz := all d (by simp)
      exact False.elim ((List.nodup_cons.mp nd).1 (by simp [dz]))

open Classical in
theorem availableIndicator {n : Nat} (hn : 1 ≤ n) (b : Mask (board n))
    (legal : Legal b) (size : pieces b = n-1) :
    available b = (if Completable b then 1 else 0) := by
  classical
  let test : Mask (board n) → Bool := fun u => decide (Legal u)
  let cs := destinations b test
  have countEq : available b = cs.length := by
    simpa [available, cs, test] using (destinationLength b test).symm
  obtain ⟨z, unique⟩ := uniqueEmptyCross hn legal size
  have same (c : Cell n) (hc : c ∈ cs) : c = z := by
    obtain ⟨u, _, ok, perm⟩ := insertionWitness b test c hc
    have hu : Legal u := by simpa [test] using ok
    apply (unique c).mp
    exact ⟨(List.nodup_cons.mp ((perm.map Prod.fst).nodup (distinctRows hu))).1,
           (List.nodup_cons.mp ((perm.map Prod.snd).nodup (distinctColumns hu))).1⟩
  have possible : Completable b ↔ ∃ c, c ∈ cs := by
    constructor
    · rintro ⟨u, step, ok, _⟩
      exact destExists step test (by simpa [test] using ok)
    · rintro ⟨c, hc⟩
      obtain ⟨u, step, ok, _⟩ := insertionWitness b test c hc
      exact ⟨u, step, by simpa [test] using ok, by rw [step.size, size]; omega⟩
  rw [countEq]
  rcases singleList cs z (List.Pairwise.sublist (destinationSublist b test) (board_unique n)) same with e | e
  · have h : ¬ Completable b := fun h => by simpa [e] using possible.mp h
    simp [e, h]
  · have h := possible.mpr ⟨z, by simp [e]⟩
    simp [e, h]

noncomputable def goodCount (n : Nat) : Nat := by
  classical
  exact sumMasks (board n) (fun b => layer (n-1) b * (if Completable b then 1 else 0))

theorem countCompletable (n : Nat) (hn : 1 ≤ n) : goodCount n = n * count n n := by
  classical
  have point (b : Mask (board n)) :
      layer (n-1) b * (if Completable b then 1 else 0) = layer (n-1) b * available b := by
    by_cases h : Legal b ∧ pieces b = n-1
    · rw [availableIndicator hn b h.1 h.2]
    · simp [layer, h]
  have idx : n-1+1 = n := by omega
  simpa only [goodCount, point, Nat.sub_self, Nat.sub_zero, idx] using interpretation n 1 (by decide) hn

/-- Fraction of marked crosses that admit a queen, using the paper's count ratio.
Proof arguments enforce positive denominators for the uniform distribution. -/
noncomputable def fh (n h : Nat) (_ : 0 < h) (_ : 0 < count n (n-h)) : Std.Internal.Rat :=
  Std.Internal.mkRat (Int.ofNat ((n-h+1) * count n (n-(h-1)))) (h^2 * count n (n-h))

noncomputable def completionProbability (n : Nat) (_ : 0 < count n (n-1)) : Std.Internal.Rat :=
  Std.Internal.mkRat (Int.ofNat (goodCount n)) (count n (n-1))

theorem fOne_eq_completionProbability (n : Nat) (hn : 1 ≤ n) (pos : 0 < count n (n-1)) :
    fh n 1 (by decide) pos = completionProbability n pos := by
  have idx : n-1+1 = n := by omega
  simp [fh, completionProbability, countCompletable n hn, idx]

theorem fh_eq_uniformCrossFraction (n h : Nat) (hh : 0 < h) (hn : h ≤ n)
    (pos : 0 < count n (n-h)) :
    fh n h hh pos = Std.Internal.mkRat
      (Int.ofNat (sumMasks (board n) (fun b => layer (n-h) b * available b)))
      (h^2 * count n (n-h)) := by
  rw [interpretation n h hh hn]
  rfl

end ArticuloA

#print axioms ArticuloA.availableIndicator
#print axioms ArticuloA.countCompletable
#print axioms ArticuloA.fOne_eq_completionProbability
#print axioms ArticuloA.fh_eq_uniformCrossFraction
