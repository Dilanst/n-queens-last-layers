import IncidenciaMarcas

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

def consumeVertex {n} : Choice n → Fin 4 → Nat → Prop
  | .real c,i,v => lines c i = v
  | .virtual g,i,v => g i = v
  | .fail,_,_ => False
def isReal {n} : Choice n → Prop
  | .real _ => True
  | _ => False
def eraseDest {n} (z e : Cell n) (m : Marks) (a : Choice n) (j : Fin 4) :=
  consumeVertex a (side j) (key z e j) ∧ (m j = true ∨ isReal a)
def eraseOwn {n} (e : Cell n) (a : Choice n) (i : Fin 4) := consumeVertex a i (lines e i)
def bornHere {n} (e : Cell n) : Choice n → Prop
  | .real c => e=c
  | _ => False

private theorem active_after {n} (x : State n) (a : Choice n) (i : Fin 4) (v : Nat) :
    (next x a).active i v = true ↔ x.active i v = true ∧ ¬consumeVertex a i v := by
  cases a <;> simp [next,consume,consumeVertex,ne_comm]

private theorem vacancy_after {n} (x : State n) (a : Choice n) (fresh : admissible x a)
    (i : Fin 4) (v : Nat) : vacant (next x a).physical i v ↔
    vacant x.physical i v ∧ ¬(consumeVertex a i v ∧ isReal a) := by
  cases a with
  | fail => simp [next,consumeVertex,isReal]
  | virtual _ => simp [next,isReal]
  | real c =>
    constructor
    · intro h
      have old : vacant x.physical i v := fun e he => h e ((inserted _ c fresh e).mpr (.inr he))
      exact ⟨old, fun w => h c ((inserted _ c fresh c).mpr (.inl rfl)) w.1⟩
    · rintro ⟨old,miss⟩
      exact (vacant_insert _ c fresh i v (fun eq => miss ⟨eq,trivial⟩)).mpr old

theorem marks_after {n} (x : State n) (a : Choice n) (fresh : admissible x a)
    (z e : Cell n) (m : Marks) : marked (next x a) z e m ↔
    marked x z e m ∧ ∀ j, ¬eraseDest z e m a j := by
  have one (j : Fin 4) :
      (if m j then (next x a).active (side j) (key z e j) = true
       else vacant (next x a).physical (side j) (key z e j)) ↔
      (if m j then x.active (side j) (key z e j) = true
       else vacant x.physical (side j) (key z e j)) ∧ ¬eraseDest z e m a j := by
    cases h : m j <;> simp [eraseDest,h,active_after,vacancy_after x a fresh]
  constructor
  · exact fun h => ⟨fun j => ((one j).mp (h j)).1, fun j => ((one j).mp (h j)).2⟩
  · exact fun h j => (one j).mpr ⟨h.1 j,h.2 j⟩

theorem available_after {n} (x : State n) (a : Choice n) (e : Cell n) :
    available (next x a) (lines e) = true ↔ available x (lines e) = true ∧ ∀ i, ¬eraseOwn e a i := by
  simp only [available,List.all_eq_true,active_after]
  have mem (i : Fin 4) : i ∈ List.finRange 4 := by simp [List.finRange,List.mem_ofFn] <;> omega
  exact ⟨fun h => ⟨fun j hj => (h j hj).1,fun j => (h j (mem j)).2⟩,
    fun h j hj => ⟨h.1 j hj,h.2 j⟩⟩

theorem available_pattern_step {n} (x : State n) (a : Choice n) (fresh : admissible x a)
    (z e : Cell n) (m : Marks) : availPattern (next x a) z e m ↔
    availPattern x z e m ∧ (∀ i, ¬eraseOwn e a i) ∧ ∀ j, ¬eraseDest z e m a j := by
  simp only [availPattern,available_after,marks_after _ _ fresh]
  constructor
  · rintro ⟨g,⟨av,own⟩,mk,sec⟩; exact ⟨⟨g,av,mk⟩,own,sec⟩
  · rintro ⟨⟨g,av,mk⟩,own,sec⟩; exact ⟨g,⟨av,own⟩,mk,sec⟩

theorem occupied_pattern_step {n} (x : State n) (a : Choice n) (good : coherent x)
    (live : allowed x a) (z e : Cell n) (m : Marks) : occupied (next x a) z e m ↔
    (occupied x z e m ∧ ∀ j, ¬eraseDest z e m a j) ∨
    (bornHere e a ∧ availPattern x z e m) := by
  have fresh := choice_adm good a live
  simp only [occupied,marks_after _ _ fresh,availPattern]
  cases a with
  | fail => simp [bornHere,next,eraseDest,consumeVertex]
  | virtual g =>
    simp only [next,bornHere,false_and,or_false]
    exact ⟨fun ⟨o,g',mk,sec⟩ => ⟨⟨o,g',mk⟩,sec⟩,
      fun ⟨⟨o,g',mk⟩,sec⟩ => ⟨o,g',mk,sec⟩⟩
  | real c =>
    change ((e ∈ queens (toggle c x.physical)) ∧ _) ↔ _
    rw [inserted x.physical c fresh e]
    constructor
    · rintro ⟨(rfl|old),G,mk,sec⟩
      · exact .inr ⟨rfl,G,live,mk⟩
      · exact .inl ⟨⟨old,G,mk⟩,sec⟩
    · rintro (⟨⟨old,G,mk⟩,sec⟩ | ⟨rfl,G,_,mk⟩)
      · exact ⟨.inr old,G,mk,sec⟩
      · exact ⟨.inl rfl,G,mk,fun j he => newborn_away z _ G j he.1.symm⟩

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.occupied_pattern_step
#print axioms ArticuloA.Trayectoria.E2.available_pattern_step
