import MarcasOcupadas

namespace ArticuloA.Trayectoria.E2
open ArticuloA

def slot {n} (z e : Cell n) : Fin 8 → Nat
  | 0 => lines e 0 | 1 => lines e 1 | 2 => lines e 2 | 3 => lines e 3
  | 4 => key z e 0 | 5 => key z e 1 | 6 => key z e 2 | 7 => key z e 3
def family : Fin 8 → Fin 4
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 2 | 5 => 3 | 6 => 2 | 7 => 3
def along {n} (i : Fin 8) (e : Cell n) := if i = 0 ∨ i = 6 ∨ i = 7 then e.2 else e.1

private theorem fibre_inj {n} (z e f : Cell n) (i : Fin 8)
    (line : slot z e i = slot z f i) (coord : along i e = along i f) : e = f := by
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [along] at coord <;> simp [slot,key,dest,side,lines] at line <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem distinct_le {ι} [DecidableEq ι] (xs items : List ι) (nd : xs.Nodup)
    (within : ∀ i ∈ xs, i ∈ items) : xs.length ≤ items.length := by
  induction xs generalizing items with
  | nil => simp
  | cons i xs ih =>
    obtain ⟨absent,nd'⟩ := List.nodup_cons.mp nd
    have hi := within i (by simp)
    have small := ih (items.erase i) nd' (by
      intro j hj; have ne : j ≠ i := fun eq => absent (eq ▸ hj)
      exact (List.mem_erase_of_ne ne).mpr (within j (by simp [hj])))
    rw [List.length_erase_of_mem hi] at small
    have pos := List.length_pos_of_mem hi
    simp; omega

theorem fibre_count {n} (z : Cell n) (i : Fin 8) (v : Nat) :
    (board n).countP (fun e => slot z e i == v) ≤ n := by
  let xs := (board n).filter (fun e => slot z e i == v)
  have nd : xs.Nodup := (board_unique n).filter _
  have nd' : (xs.map (along i)).Nodup := by
    apply List.pairwise_map.mpr
    apply nd.imp_of_mem
    intro e f he hf distinct eq
    have le := beq_iff_eq.mp (List.mem_filter.mp he).2
    have lf := beq_iff_eq.mp (List.mem_filter.mp hf).2
    exact distinct (fibre_inj z e f i (le.trans lf.symm) eq)
  have bound := distinct_le (xs.map (along i)) (List.finRange n) nd' (by
    intro j _; simp [List.finRange,List.mem_ofFn])
  simpa [List.countP_eq_length_filter,xs] using bound

private theorem count_or {ι} (L : List ι) (A B : ι → Bool) :
    L.countP (fun i => A i || B i) ≤ L.countP A + L.countP B := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.countP_cons]; cases ha : A i <;> cases hb : B i <;> simp [ha,hb] <;> omega

private theorem many {ι β} (L : List ι) (keys : List β) (hit : β → ι → Bool) (n : Nat)
    (one : ∀ j, L.countP (hit j) ≤ n) :
    L.countP (fun e => keys.any (fun j => hit j e)) ≤ keys.length*n := by
  induction keys with
  | nil => simp
  | cons j keys ih =>
    have h := count_or L (hit j) (fun e => keys.any (fun k => hit k e))
    simp only [List.any_cons,List.length_cons,Nat.succ_mul]
    have hj := one j; omega

theorem eight_fibres {n} (z : Cell n) (g : Edge) (flip : Cell n → Bool)
    (cover : ∀ e, flip e → ∃ i, slot z e i = g (family i)) : (board n).countP flip ≤ 8*n := by
  let hit := fun (j : Fin 8) e => slot z e j == g (family j)
  have h := many (board n) (List.finRange 8) hit n (fun j => fibre_count z j _)
  rw [List.length_finRange] at h
  apply Nat.le_trans (List.countP_mono_left (q := fun e => (List.finRange 8).any (fun i => hit i e)) ?_) h
  intro e _ he; obtain ⟨i,hi⟩ := cover e he
  exact List.any_eq_true.mpr ⟨i,by simp [List.finRange,List.mem_ofFn] <;> omega,beq_iff_eq.mpr hi⟩

def availPattern {n} (x : State n) (z e : Cell n) (mask : Fin 4 → Bool) : Prop :=
  compatible (Repair.corners (z,e)).1 (Repair.corners (z,e)).2 ∧
  available x (lines e) = true ∧ marked x z e mask

open Classical in
noncomputable def availChanged {n} (x y : State n) (z e : Cell n) (mask : Fin 4 → Bool) :=
  decide (¬(availPattern x z e mask ↔ availPattern y z e mask))

private theorem away_all {n} (z e : Cell n) (g : Edge)
    (away : ¬∃ i, slot z e i = g (family i)) :
    (∀ j, lines e j ≠ g j) ∧ (∀ j, key z e j ≠ g (side j)) := by
  constructor <;> intro j eq <;>
    have cases4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rcases cases4 with rfl|rfl|rfl|rfl
    · exact away ⟨0,eq⟩
    · exact away ⟨1,eq⟩
    · exact away ⟨2,eq⟩
    · exact away ⟨3,eq⟩
  · rcases cases4 with rfl|rfl|rfl|rfl
    · exact away ⟨4,eq⟩
    · exact away ⟨5,eq⟩
    · exact away ⟨6,eq⟩
    · exact away ⟨7,eq⟩

private theorem avail_unchanged {n} (x y : State n) (z e : Cell n) (mask : Fin 4 → Bool)
    (own : ∀ j, x.active j (lines e j) = y.active j (lines e j))
    (pat : marked y z e mask ↔ marked x z e mask) : availPattern x z e mask ↔ availPattern y z e mask := by
  have act : available x (lines e) = available y (lines e) :=
    congrArg (fun u => (List.finRange 4).all u) (funext own)
  simp only [availPattern,act,pat]

theorem real_avail_jump {n} (x : State n) (g z : Cell n) (empty : g ∉ queens x.physical)
    (mask : Fin 4 → Bool) :
    (board n).countP (fun e => availChanged x (next x (.real g)) z e mask) ≤ 8*n := by
  classical
  apply eight_fibres z (lines g)
  intro e he; apply Classical.byContradiction; intro miss
  obtain ⟨own,tar⟩ := away_all z e (lines g) miss
  apply of_decide_eq_true he
  apply avail_unchanged _ _ _ _ _ (by intro j; simp [next,consume,own j])
  exact same_marks _ _ _ _ _ (by intro j; simp [next,consume,tar j])
    (fun j => vacant_insert _ _ empty _ _ (Ne.symm (tar j)))

theorem virtual_avail_jump {n} (x : State n) (g : Edge) (z : Cell n) (mask : Fin 4 → Bool) :
    (board n).countP (fun e => availChanged x (next x (.virtual g)) z e mask) ≤ 8*n := by
  classical
  apply eight_fibres z g
  intro e he; apply Classical.byContradiction; intro miss
  obtain ⟨own,tar⟩ := away_all z e g miss
  apply of_decide_eq_true he
  apply avail_unchanged _ _ _ _ _ (by intro j; simp [next,consume,own j])
  exact same_marks _ _ _ _ _ (by intro j; simp [next,consume,tar j]) (fun _ => Iff.rfl)

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.eight_fibres
#print axioms ArticuloA.Trayectoria.E2.real_avail_jump
#print axioms ArticuloA.Trayectoria.E2.virtual_avail_jump
