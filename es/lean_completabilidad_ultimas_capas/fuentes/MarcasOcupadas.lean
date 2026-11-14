import ProcesoE2

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

def side : Fin 4 → Fin 4 | 0 => 2 | 1 => 3 | 2 => 2 | 3 => 3
def dest {n} (z e : Cell n) : Fin 4 → Cell n
  | 0 | 1 => (z.1,e.2)
  | 2 | 3 => (e.1,z.2)
def key {n} (z e : Cell n) (j : Fin 4) := lines (dest z e j) (side j)

def vacant {n} (p : Placement n) (i : Fin 4) (v : Nat) : Prop :=
  ∀ u ∈ queens p, lines u i ≠ v
def marked {n} (x : State n) (z e : Cell n) (mask : Fin 4 → Bool) : Prop :=
  ∀ j, if mask j then x.active (side j) (key z e j) = true
    else vacant x.physical (side j) (key z e j)
def occupied {n} (x : State n) (z e : Cell n) (mask : Fin 4 → Bool) : Prop :=
  e ∈ queens x.physical ∧ compatible (corners (z,e)).1 (corners (z,e)).2 ∧ marked x z e mask

private theorem key_unique {n} {p : Placement n} (legal : Legal p) (z : Cell n) (j : Fin 4)
    {e f : Cell n} (he : e ∈ queens p) (hf : f ∈ queens p) (eq : key z e j = key z f j) : e = f := by
  apply Classical.byContradiction
  intro ne
  have c := legal_pair legal he hf ne
  have r : e.1.val ≠ f.1.val := fun w => c.1 (Fin.ext w)
  have k : e.2.val ≠ f.2.val := fun w => c.2.1 (Fin.ext w)
  have cases4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases4 with rfl | rfl | rfl | rfl <;> simp [key,dest,lines,side] at eq <;> omega

private theorem singleton_count {ι} (xs : List ι) (u : ι → Bool) (nd : xs.Nodup)
    (unique : ∀ a b, u a = true → u b = true → a = b) : xs.countP u ≤ 1 := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    obtain ⟨absent,nd'⟩ := List.nodup_cons.mp nd
    rw [List.countP_cons]
    cases hi : u i with
    | false => simpa using ih nd'
    | true =>
      have no : xs.countP u = 0 := List.countP_eq_zero.mpr (by
        intro j hj yes; exact absent ((unique j i yes hi) ▸ hj))
      simp [no]

private theorem sum_cover {ι} (xs : List ι) (P A B C D E : ι → Bool)
    (cover : ∀ i, P i → A i ∨ B i ∨ C i ∨ D i ∨ E i) :
    xs.countP P ≤ xs.countP A + xs.countP B + xs.countP C + xs.countP D + xs.countP E := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.countP_cons]
    cases hp : P i <;> simp [hp]
    · split <;> split <;> split <;> split <;> split <;> omega
    · rcases cover i hp with h|h|h|h|h <;> simp [h] <;> omega

/-- A real edge or an arbitrary virtual tuple has just one removed D vertex
and one removed A vertex. The four slots may be hit, each by at most one OLD
queen; only a real move also has a possible newborn. -/
theorem flips_le_five {n} (p : Placement n) (legal : Legal p) (z : Cell n)
    (edge : Edge) (born : Option (Cell n)) (flip : Cell n → Bool)
    (cover : ∀ e, flip e → born = some e ∨
      (e ∈ queens p ∧ ∃ j, key z e j = edge (side j))) : (board n).countP flip ≤ 5 := by
  classical
  let bornAt := fun e => decide (born = some e)
  let atSlot := fun (j : Fin 4) e => decide (e ∈ queens p ∧ key z e j = edge (side j))
  have h := sum_cover (board n) flip bornAt (atSlot 0) (atSlot 1) (atSlot 2) (atSlot 3) (by
    intro e he; rcases cover e he with b | ⟨old,j,hj⟩
    · exact .inl (decide_eq_true b)
    · have jj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases jj with rfl | rfl | rfl | rfl <;> simp [atSlot,old,hj])
  have one := singleton_count (board n) bornAt (board_unique n) (by
    intro a b ha hb; simp [bornAt] at ha hb; exact Option.some.inj (ha.symm.trans hb))
  have each (j : Fin 4) := singleton_count (board n) (atSlot j) (board_unique n) (by
    intro a b ha hb; simp [atSlot] at ha hb; exact key_unique legal z j ha.1 hb.1 (ha.2.trans hb.2.symm))
  have h0 := each 0; have h1 := each 1; have h2 := each 2; have h3 := each 3
  omega

theorem vacant_insert {n} (p : Placement n) (g : Cell n) (empty : g ∉ queens p)
    (i : Fin 4) (v : Nat) (away : lines g i ≠ v) : vacant (toggle g p) i v ↔ vacant p i v := by
  constructor
  · exact fun h e he => h e ((inserted p g empty e).mpr (.inr he))
  · intro h e he
    rcases (inserted p g empty e).mp he with rfl | old
    · exact away
    · exact h e old

theorem same_marks {n} (x y : State n) (z e : Cell n) (mask : Fin 4 → Bool)
    (act : ∀ j, y.active (side j) (key z e j) = x.active (side j) (key z e j))
    (vac : ∀ j, vacant y.physical (side j) (key z e j) ↔ vacant x.physical (side j) (key z e j)) :
    marked y z e mask ↔ marked x z e mask := by
  unfold marked
  apply forall_congr'; intro j; cases h : mask j <;> simp [act,vac]

open Classical in
noncomputable def changed {n} (x y : State n) (z : Cell n) (mask : Fin 4 → Bool) (e : Cell n) :=
  decide (¬(occupied y z e mask ↔ occupied x z e mask))

theorem real_marks_jump {n} (x : State n) (legal : Legal x.physical) (g z : Cell n)
    (empty : g ∉ queens x.physical) (mask : Fin 4 → Bool) :
    (board n).countP (changed x (next x (.real g)) z mask) ≤ 5 := by
  classical
  apply flips_le_five x.physical legal z (lines g) (some g)
  intro e he; have diff := of_decide_eq_true he
  by_cases same : g = e
  · exact .inl (congrArg some same)
  right
  have occ : e ∈ queens (next x (.real g)).physical ↔ e ∈ queens x.physical := by
    simpa [next,Ne.symm same] using inserted x.physical g empty e
  by_cases old : e ∈ queens x.physical
  · refine ⟨old,Classical.byContradiction (fun miss => ?_)⟩
    have away (j) : key z e j ≠ lines g (side j) := fun eq => miss ⟨j,eq⟩
    have eq := same_marks x (next x (.real g)) z e mask
      (by intro j; simp [next,consume,away j])
      (fun j => vacant_insert _ _ empty _ _ (Ne.symm (away j)))
    exact diff (by simp only [occupied,occ,eq])
  · exact (diff (by simp [occupied,occ,old])).elim

theorem virtual_marks_jump {n} (x : State n) (legal : Legal x.physical) (g : Edge)
    (z : Cell n) (mask : Fin 4 → Bool) :
    (board n).countP (changed x (next x (.virtual g)) z mask) ≤ 5 := by
  classical
  apply flips_le_five x.physical legal z g none
  intro e he; have diff := of_decide_eq_true he
  right
  by_cases old : e ∈ queens x.physical
  · refine ⟨old,Classical.byContradiction (fun miss => ?_)⟩
    have away (j) : key z e j ≠ g (side j) := fun eq => miss ⟨j,eq⟩
    have eq := same_marks x (next x (.virtual g)) z e mask
      (by intro j; simp [next,consume,away j]) (fun _ => Iff.rfl)
    exact diff (by simp only [occupied,eq]; rfl)
  · exact (diff (by simp [occupied,next,old])).elim

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.flips_le_five
#print axioms ArticuloA.Trayectoria.E2.real_marks_jump
#print axioms ArticuloA.Trayectoria.E2.virtual_marks_jump
