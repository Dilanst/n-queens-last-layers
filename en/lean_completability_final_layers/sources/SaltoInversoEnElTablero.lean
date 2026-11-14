import CambioInversoFisico
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

theorem inserted {n xs} (p : @Mask (Cell n) xs) (g : Cell n)
    (mem : g ∈ xs) (fresh : g ∉ queens p) :
    (queens (toggle g p)).Perm (g::queens p) := by
  induction p with
  | empty => contradiction
  | @skip e xs p ih =>
    by_cases eq : e=g
    · subst e; simp [toggle,queens]
    · exact (by simpa [toggle,queens,eq] using ih ((List.mem_cons.mp mem).resolve_left (Ne.symm eq)) fresh)
  | @take e xs p ih =>
    have eq : e ≠ g := by intro h; exact fresh (by simp [queens,h])
    have H := ih ((List.mem_cons.mp mem).resolve_left (Ne.symm eq)) (fun h => fresh (List.mem_cons_of_mem _ h))
    simpa [toggle,queens,eq] using (H.cons e).trans (List.Perm.swap _ _ _)

private theorem sum_perm {u v : List Nat} (h : u.Perm v) : u.sum = v.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ ih jh => exact ih.trans jh

private theorem pair_perm {n} (test : Cell n → Cell n → Bool) {u v : List (Cell n)} (h : u.Perm v) :
    pairSum u u test = pairSum v v test := by
  unfold pairSum
  have eq : (fun e => u.countP (test e)) = (fun e => v.countP (test e)) :=
    funext (fun e => List.Perm.countP_eq (test e) h)
  rw [eq]; exact sum_perm (h.map _)

private theorem monotone {n} (u v : List (Cell n)) (P Q : Cell n → Cell n → Bool)
    (h : ∀ e f, P e f → Q e f) : pairSum u v P ≤ pairSum u v Q := by
  induction u with
  | nil => exact Nat.le_refl 0
  | cons e es ih => exact Nat.add_le_add (List.countP_mono_left (fun f _ => h e f)) ih

private theorem split {n} (u v : List (Cell n)) (P Q : Cell n → Cell n → Bool) :
    pairSum u v P ≤ pairSum u v Q + pairSum u v (fun e f => P e f && !Q e f) := by
  have row (e) (xs : List (Cell n)) : xs.countP (P e) ≤ xs.countP (Q e) +
      xs.countP (fun f => P e f && !Q e f) := by
    induction xs with
    | nil => simp
    | cons f fs ih => simp only [List.countP_cons]; cases P e f <;> cases Q e f <;> simp_all <;> omega
  induction u with
  | nil => exact Nat.le_refl 0
  | cons e es ih =>
    change _ + pairSum es v P ≤ (_ + pairSum es v Q) + (_ + pairSum es v _)
    have := row e v; dsimp only; omega

noncomputable def inversas {n} (p : Placement n) := pairSum (queens p) (queens p) (eligiblePair p)

theorem paso_inverso {n} (p : Placement n) (legal : Legal p) (g : Cell n) (fresh : g ∉ queens p) :
    inversas (toggle g p) ≤ inversas p + 2*n ∧ inversas p ≤ inversas (toggle g p) + 2*n := by
  let L := queens p
  let test := eligiblePair (toggle g p)
  have same : inversas (toggle g p) = pairSum (g::L) (g::L) test :=
    pair_perm _ (inserted p g (board_complete g) fresh)
  have mono : pairSum L L test ≤ inversas p := by
    apply monotone
    intro e f h
    simp only [test,eligiblePair,decide_eq_true_eq] at h ⊢
    refine ⟨h.1,?_⟩
    intro z hz
    apply h.2 z
    have ne : z ≠ g := fun eq => fresh (eq ▸ hz)
    exact (mem_toggle g z p).mpr (by simp [ne,hz])
  have left := new_pairs p legal g test (by simp [test,eligiblePair])
  have right := split L L (eligiblePair p) test
  have loss := old_lost p legal g
  have keep : pairSum L L test ≤ pairSum (g::L) (g::L) test := by
    have addCol (xs : List (Cell n)) : pairSum xs L test ≤ pairSum xs (g::L) test := by
      induction xs with
      | nil => exact Nat.le_refl 0
      | cons x xs ih =>
        apply Nat.add_le_add _ ih; dsimp only; rw [List.countP_cons]; omega
    change _ ≤ _ + pairSum L (g::L) test
    exact Nat.le_trans (addCol _) (Nat.le_add_left _ _)
  change pairSum L L (fun e f => eligiblePair p e f && !test e f) ≤ 2*n at loss
  change pairSum (g::L) (g::L) test ≤ pairSum L L test + 2*n at left
  change inversas p ≤ _ + _ at right
  omega
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.paso_inverso
