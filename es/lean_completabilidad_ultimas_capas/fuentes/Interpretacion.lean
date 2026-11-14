import Std

/- Article A, interpretation lemma (Section 2). Counts are in Nat to keep empty layers valid. -/
namespace ArticuloA

inductive Mask {α : Type} : List α → Type where
  | empty : Mask []
  | skip {x : α} {xs : List α} : Mask xs → Mask (x :: xs)
  | take {x : α} {xs : List α} : Mask xs → Mask (x :: xs)

def pieces {α : Type} {xs : List α} : Mask xs → Nat
  | .empty => 0
  | .skip b => pieces b
  | .take b => pieces b + 1

def sumMasks {α : Type} : (xs : List α) → (Mask xs → Nat) → Nat
  | [], w => w .empty
  | _ :: xs, w =>
      sumMasks xs (fun b => w (.skip b)) + sumMasks xs (fun b => w (.take b))

/-- Sum w over configurations obtained by setting exactly one vacant cell to occupied. -/
def addSum {α : Type} {xs : List α} (b : Mask xs) (w : Mask xs → Nat) : Nat :=
  match b with
  | .empty => 0
  | .skip t => w (.take t) + addSum t (fun u => w (.skip u))
  | .take t => addSum t (fun u => w (.take u))

private theorem sum_add {α : Type} (xs : List α) (f g : Mask xs → Nat) :
    sumMasks xs (fun b => f b + g b) = sumMasks xs f + sumMasks xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumMasks]
    rw [ih (fun b => f (.skip b)) (fun b => g (.skip b)),
        ih (fun b => f (.take b)) (fun b => g (.take b))]
    omega

private theorem sum_scale {α : Type} (xs : List α) (k : Nat) (f : Mask xs → Nat) :
    sumMasks xs (fun b => k * f b) = k * sumMasks xs f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumMasks, ih, Nat.mul_add]

/-- Adding one cell on the left counts each upper mask once per occupied cell. -/
theorem incidence {α : Type} (xs : List α) (w : Mask xs → Nat) :
    sumMasks xs (fun b => addSum b w) = sumMasks xs (fun b => pieces b * w b) := by
  induction xs with
  | nil => simp [sumMasks, addSum, pieces]
  | cons x xs ih =>
    simp only [sumMasks, addSum, pieces, Nat.succ_mul]
    rw [sum_add, ih (fun b => w (.skip b)), ih (fun b => w (.take b)), sum_add]
    omega

abbrev Cell (n : Nat) := Fin n × Fin n

def board (n : Nat) : List (Cell n) :=
  (List.finRange n).flatMap (fun r => (List.finRange n).map (fun c => (r,c)))

theorem board_complete {n : Nat} (c : Cell n) : c ∈ board n := by
  rcases c with ⟨r,c⟩
  simp [board, List.mem_flatMap, List.mem_map, List.finRange, List.mem_ofFn]

private theorem indices_unique (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij heq
  have e := congrArg Fin.val heq
  simp only [List.getElem_finRange] at e
  exact (Nat.ne_of_lt hij) e

theorem board_unique (n : Nat) : (board n).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro r _
    apply List.pairwise_map.mpr
    exact (indices_unique n).imp (fun h heq => h (congrArg Prod.snd heq))
  · apply (indices_unique n).imp
    intro r s h p hp q hq heq
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    exact h (congrArg Prod.fst heq)

def compatible {n : Nat} (a b : Cell n) : Prop :=
  a.1 ≠ b.1 ∧ a.2 ≠ b.2 ∧
  a.1.val + b.2.val ≠ b.1.val + a.2.val ∧
  a.1.val + a.2.val ≠ b.1.val + b.2.val

def queens {n : Nat} {xs : List (Cell n)} : Mask xs → List (Cell n)
  | .empty => []
  | .skip b => queens b
  | .take (x := x) b => x :: queens b

def Legal {n : Nat} {xs : List (Cell n)} (b : Mask xs) : Prop :=
  (queens b).Pairwise compatible

noncomputable def layer {n : Nat} {xs : List (Cell n)} (q : Nat) (b : Mask xs) : Nat := by
  classical
  exact if Legal b ∧ pieces b = q then 1 else 0

noncomputable def count (n q : Nat) := sumMasks (board n) (layer q)

private theorem layer_degree {n : Nat} {xs : List (Cell n)} (q : Nat) (b : Mask xs) :
    pieces b * layer q b = q * layer q b := by
  classical
  by_cases h : Legal b ∧ pieces b = q
  · rw [h.2]
  · simp [layer, h]

/-- The raw form of the interpretation lemma, indexed by the upper number of queens. -/
theorem count_extensions (n q : Nat) :
    sumMasks (board n) (fun b => addSum b (layer (q+1))) = (q+1) * count n (q+1) := by
  rw [incidence]
  simp only [layer_degree (q+1)]
  exact sum_scale _ _ _

/-- A single marked insertion; every other bit is unchanged. -/
inductive Adds {α : Type} : {xs : List α} → Mask xs → Mask xs → Prop where
  | here {x : α} {xs : List α} (b : Mask xs) : Adds (.skip (x := x) b) (.take b)
  | skip {x : α} {xs : List α} {b u : Mask xs} :
      Adds b u → Adds (.skip (x := x) b) (.skip u)
  | take {x : α} {xs : List α} {b u : Mask xs} :
      Adds b u → Adds (.take (x := x) b) (.take u)

theorem Adds.size {α : Type} {xs : List α} {b u : Mask xs} (step : Adds b u) :
    pieces u = pieces b + 1 := by
  induction step with
  | here => rfl
  | skip _ ih => exact ih
  | take _ ih => simp only [pieces, ih]

theorem Adds.sublist {n : Nat} {xs : List (Cell n)} {b u : Mask xs}
    (step : Adds b u) : (queens b).Sublist (queens u) := by
  induction step with
  | here => exact List.Sublist.cons _ (List.Sublist.refl _)
  | skip _ ih => exact ih
  | take _ ih => exact List.Sublist.cons₂ _ ih

private theorem addSum_congr {α : Type} {xs : List α} (b : Mask xs)
    (f g : Mask xs → Nat) (h : ∀ u, Adds b u → f u = g u) :
    addSum b f = addSum b g := by
  induction b with
  | empty => rfl
  | skip t ih =>
    simp only [addSum]
    rw [h _ (.here t)]
    exact congrArg (_ + ·) (ih _ _ (fun u step => h (.skip u) (.skip step)))
  | take t ih => exact ih _ _ (fun u step => h (.take u) (.take step))

private theorem addSum_scale {α : Type} {xs : List α} (b : Mask xs) (k : Nat)
    (f : Mask xs → Nat) : addSum b (fun u => k * f u) = k * addSum b f := by
  induction b with
  | empty => simp [addSum]
  | skip _ ih => simp only [addSum, ih, Nat.mul_add]
  | take _ ih => exact ih _

/-- Number of vacant cells whose addition leaves a legal configuration. -/
noncomputable def available {n : Nat} {xs : List (Cell n)} (b : Mask xs) : Nat := by
  classical
  exact addSum b (fun u => if Legal u then 1 else 0)

private theorem one_step_layer {n : Nat} {xs : List (Cell n)} (q : Nat) (b : Mask xs) :
    addSum b (layer (q+1)) = layer q b * available b := by
  classical
  unfold available
  rw [← addSum_scale]
  apply addSum_congr
  intro u step
  by_cases hu : Legal u
  · have hb : Legal b := List.Pairwise.sublist step.sublist hu
    simp [layer, hu, hb, step.size]
  · simp [layer, hu]

/-- Section 2, interpretation lemma, integer form with h holes.
Each legal lower placement contributes exactly its number of available crosses. -/
theorem interpretation (n h : Nat) (hh : 1 ≤ h) (hn : h ≤ n) :
    sumMasks (board n) (fun b => layer (n-h) b * available b) =
      (n-h+1) * count n (n-(h-1)) := by
  have index : n-(h-1) = n-h+1 := by omega
  rw [index]
  simpa only [one_step_layer] using count_extensions n (n-h)

end ArticuloA

#print axioms ArticuloA.interpretation
