import UnHueco
import DobleCuenta

namespace ArticuloA.Repair

def counting : SumLaw Nat := ⟨0, Nat.add, Nat.zero_add, Nat.add_comm, Nat.add_assoc⟩

def pairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x,y)))

private theorem pairs_nodup {α β : Type} {xs : List α} {ys : List β}
    (hx : xs.Nodup) (hy : ys.Nodup) : (pairs xs ys).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro x _
    apply List.pairwise_map.mpr
    exact hy.imp (fun ne eq => ne (congrArg Prod.snd eq))
  · apply hx.imp
    intro a b ne p hp q hq eq
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
    exact ne (congrArg Prod.fst eq)

private theorem uniformLength {α β : Type} (xs : List α) (L : α → List β) (m : Nat)
    (h : ∀ x ∈ xs, (L x).length = m) : (xs.flatMap L).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx])), Nat.add_comm]

theorem pairs_length {α β : Type} (xs : List α) (ys : List β) :
    (pairs xs ys).length = xs.length * ys.length := uniformLength _ _ _ (by simp)

theorem subset_length {α : Type} [DecidableEq α] (xs ys : List α) (nd : xs.Nodup)
    (sub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, dn⟩ := List.nodup_cons.mp nd
    have mem := sub x (by simp)
    have bound := ih (ys.erase x) dn (by
      intro y hy
      have ne : y ≠ x := fun eq => hx (eq ▸ hy)
      exact (List.mem_erase_of_ne ne).mpr (sub y (by simp [hy])))
    have lengthpos := List.length_pos_of_mem mem
    rw [List.length_erase_of_mem mem] at bound
    simp only [List.length_cons]; omega

private theorem sum_pairs {α β : Type} (xs : List α) (ys : List β) (f : α × β → Nat) :
    counting.over (pairs xs ys) f = counting.over xs (fun x => counting.over ys (fun y => f (x,y))) := by
  have foldMap (x : α) : ∀ l : List β, counting.over (l.map (fun y => (x,y))) f =
      counting.over l (fun y => f (x,y)) := by
    intro l; induction l with
    | nil => rfl
    | cons y l ih => change _ + counting.over _ _ = _ + counting.over _ _; rw [ih]
  have append (as bs : List (α × β)) : counting.over (as ++ bs) f =
      counting.over as f + counting.over bs f := by
    induction as with
    | nil => simp [SumLaw.over, counting]
    | cons a as ih =>
      change f a + counting.over (as ++ bs) f = (f a + counting.over as f) + counting.over bs f
      rw [ih, Nat.add_assoc]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change counting.over ((ys.map (fun y => (x,y))) ++ pairs xs ys) f = _ + counting.over xs _
    rw [append, foldMap, ih]

private theorem marks_board {n} (f : Mark n → Nat) :
    counting.marks f = counting.over (pairs (board n) (board n)) f := by
  unfold SumLaw.marks board
  change _ = counting.over (pairs (pairs _ _) (pairs _ _)) f
  simp only [sum_pairs]

open Classical in
private theorem bound_marks {n} (P : Mark n → Prop) (candidates : List (Mark n))
    (cover : ∀ a, P a → a ∈ candidates) :
    counting.marks (fun m => if P m then 1 else 0) ≤ candidates.length := by
  rw [marks_board]
  have filterLength (xs : List (Mark n)) :
      counting.over xs (fun m => if P m then 1 else 0) =
      (xs.filter (fun m => decide (P m))).length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change (if P x then 1 else 0) + counting.over xs _ = _
      rw [ih]; by_cases hx : P x <;> simp [hx, Nat.add_comm]
  rw [filterLength]
  apply subset_length
  · exact List.Pairwise.sublist List.filter_sublist (pairs_nodup (board_unique n) (board_unique n))
  · intro x hx; exact cover x (of_decide_eq_true (List.mem_filter.mp hx).2)

private theorem lenQueens {n xs} (p : @Mask (Cell n) xs) : (queens p).length = pieces p := by
  induction p <;> simp_all [queens,pieces]

noncomputable def directDegree {n} (q : Nat) (p : Placement n) :=
  counting.marks (directWeight counting q (fun _ => 1) p)

noncomputable def inverseDegree {n} (q : Nat) (u : Placement n) :=
  counting.marks (inverseWeight counting q (fun _ => 1) u)

theorem directDegree_le {n q} (p : Placement n) (legal : Legal p) (size : pieces p = q) :
    directDegree q p ≤ (n-q)^2 * q := by
  obtain ⟨rs, _, lr, mr⟩ := freeIndices _ (distinctRows legal)
  obtain ⟨cs, _, lc, mc⟩ := freeIndices _ (distinctColumns legal)
  let pool := pairs (pairs rs cs) (queens p)
  have h := bound_marks (Direct q p) pool (by
    intro m ok
    obtain ⟨_, _, cross, queen, _⟩ := ok
    have row : m.1.1 ∈ rs := (mr _).mpr (by
      intro hh; obtain ⟨x,hx,eq⟩ := List.mem_map.mp hh; exact (cross x hx).1 eq)
    have col : m.1.2 ∈ cs := (mc _).mpr (by
      intro hh; obtain ⟨x,hx,eq⟩ := List.mem_map.mp hh; exact (cross x hx).2 eq)
    apply List.mem_flatMap.mpr
    refine ⟨m.1, List.mem_flatMap.mpr ⟨m.1.1,row,List.mem_map.mpr ⟨m.1.2,col,rfl⟩⟩, ?_⟩
    exact List.mem_map.mpr ⟨m.2,queen,rfl⟩)
  simpa [directDegree, directWeight, counting, pool, pairs_length, lr, lc, lenQueens, size, Nat.pow_two] using h

theorem inverseDegree_le {n q} (u : Placement n) :
    inverseDegree q u ≤ layer (q+1) u * ((q+1)*q) := by
  classical
  by_cases ok : Legal u ∧ pieces u = q+1
  · let occupied := queens u
    let branches (a : Cell n) := (occupied.erase a).map (fun b => (a,b))
    have len : occupied.length = q+1 := (lenQueens u).trans ok.2
    have total := uniformLength occupied branches q (by
      intro a ha
      simp [branches, List.length_erase_of_mem ha, len])
    have bound := bound_marks (Inverse q u) (occupied.flatMap branches) (by
      intro a h
      obtain ⟨_, _, ne, first, second, _⟩ := h
      exact List.mem_flatMap.mpr ⟨a.1, first, List.mem_map.mpr
        ⟨a.2, (List.mem_erase_of_ne (Ne.symm ne)).mpr second, rfl⟩⟩)
    simpa [inverseDegree, inverseWeight, counting, layer, ok, total, len] using bound
  · have impossible (a : Mark n) (h : Inverse q u a) : False := ok ⟨h.2.1, h.1⟩
    have bound := bound_marks (Inverse q u) [] (fun a h => (impossible a h).elim)
    simpa [inverseDegree, inverseWeight, counting, layer, ok] using bound

noncomputable def crossDegree {n} (q : Nat) (p : Placement n) (z : Cell n) :=
  counting.over (board n) (fun old => directWeight counting q (fun _ => 1) p (z,old))

private theorem erase_sum {α : Type} [DecidableEq α] (xs : List α) (z : α) (f : α → Nat)
    (inside : z ∈ xs) : counting.over xs f = f z + counting.over (xs.erase z) f := by
  induction xs with
  | nil => simp at inside
  | cons x xs ih =>
    by_cases eq : x = z
    · subst x; simp [SumLaw.over, counting]
    · have tail := (List.mem_cons.mp inside).resolve_left (Ne.symm eq)
      rw [List.erase_cons_tail (by simpa using eq)]
      change f x + counting.over xs f = f z + (f x + counting.over (xs.erase z) f)
      rw [ih tail]; omega

private theorem subset_lower {α : Type} [DecidableEq α] (zs xs : List α) (f : α → Nat) (t : Nat)
    (nd : zs.Nodup) (sub : ∀ z ∈ zs, z ∈ xs) (many : ∀ z ∈ zs, t ≤ f z) :
    zs.length*t ≤ counting.over xs f := by
  induction zs generalizing xs with
  | nil => simp
  | cons z zs ih =>
    obtain ⟨no, dn⟩ := List.nodup_cons.mp nd
    have iz := sub z (by simp)
    have rest := ih (xs.erase z) dn (by
      intro x hx
      have ne : x ≠ z := fun e => no (e ▸ hx)
      exact (List.mem_erase_of_ne ne).mpr (sub x (by simp [hx])))
      (fun x hx => many x (by simp [hx]))
    rw [erase_sum xs z f iz, List.length_cons, Nat.succ_mul]
    have head := many z (by simp)
    omega

theorem many_of_each_cross {n q} (p : Placement n) (legal : Legal p) (size : pieces p = q)
    (t : Nat) (enough : ∀ z, emptyCross p z → t ≤ crossDegree q p z) :
    (n-q)^2*t ≤ directDegree q p := by
  obtain ⟨rs, dr, lr, mr⟩ := freeIndices _ (distinctRows legal)
  obtain ⟨cs, dc, lc, mc⟩ := freeIndices _ (distinctColumns legal)
  have many (z : Cell n) (hz : z ∈ pairs rs cs) : t ≤ crossDegree q p z := by
    obtain ⟨r, hr, mem⟩ := List.mem_flatMap.mp hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp mem
    apply enough
    intro x hx
    exact ⟨fun e => (mr r).mp hr (List.mem_map.mpr ⟨x,hx,e⟩),
           fun e => (mc c).mp hc (List.mem_map.mpr ⟨x,hx,e⟩)⟩
  have lower := subset_lower _ (board n) _ t (pairs_nodup dr dc) (fun z _ => board_complete z) many
  rw [directDegree, marks_board, sum_pairs]
  simpa [pairs_length, lr, lc, lenQueens, size, Nat.pow_two, crossDegree] using lower

end ArticuloA.Repair

#print axioms ArticuloA.Repair.directDegree_le
#print axioms ArticuloA.Repair.inverseDegree_le
