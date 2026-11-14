import TransicionPatron

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

def pairs {ι} : List ι → List (ι × ι)
  | [] => []
  | i::ks => ks.map (fun j => (i,j)) ++ pairs ks

theorem pair_excess {ι} (ks : List ι) (hit : ι → Bool) :
    ks.countP hit - 1 ≤ (pairs ks).countP (fun ij => hit ij.1 && hit ij.2) := by
  induction ks with
  | nil => simp [pairs]
  | cons i ks ih =>
    simp only [pairs,List.countP_append,List.countP_map,List.countP_cons]
    cases h : hit i <;> simp [h,Function.comp_def] <;> omega

abbrev targets := List.finRange 4
def allSlots : List (Sum (Fin 4) (Fin 4)) := targets.map Sum.inl ++ targets.map Sum.inr
def effect {n} (z e : Cell n) (m : Marks) (a : Choice n) : Sum (Fin 4) (Fin 4) → Prop
  | .inl i => eraseOwn e a i
  | .inr j => eraseDest z e m a j

open Classical in
noncomputable def deathsOn {ι} (ks : List ι) (hit : ι → Prop) := ks.countP (fun i => decide (hit i))
open Classical in
noncomputable def doubleOn {ι} (ks : List ι) (hit : ι → Prop) :=
  (pairs ks).countP (fun ij => decide (hit ij.1 ∧ hit ij.2))

theorem excess_le_double {ι} (ks : List ι) (hit : ι → Prop) :
    deathsOn ks hit - 1 ≤ doubleOn ks hit := by
  classical
  have eq (ij : ι × ι) : (decide (hit ij.1) && decide (hit ij.2)) = decide (hit ij.1 ∧ hit ij.2) := by
    by_cases a : hit ij.1 <;> by_cases b : hit ij.2 <;> simp [a,b]
  have h := pair_excess ks (fun i => decide (hit i))
  rw [funext eq] at h
  exact h

theorem no_deaths {ι} (ks : List ι) (hit : ι → Prop) (all : ∀ i, i ∈ ks) :
    deathsOn ks hit = 0 ↔ ∀ i, ¬hit i := by
  classical
  simp only [deathsOn,List.countP_eq_zero,decide_eq_true_eq]
  exact ⟨fun h i => h i (all i),fun h i _ => h i⟩

theorem num_pairs : (pairs targets).length = 6 ∧ (pairs allSlots).length = 28 := by decide

private theorem all4 (j : Fin 4) : j ∈ targets := by simp [targets,List.finRange,List.mem_ofFn] <;> omega
private theorem all8 (i) : i ∈ allSlots := by cases i <;> simp [allSlots,all4]

/-- Unsigned balance: NEW + OLD*singles = OLD + BIRTH + OLD*excess.
The last term is positive in the drift (a correction for overcounting deaths). -/
theorem occupied_balance {n} (x : State n) (a : Choice n) (good : coherent x) (live : allowed x a)
    (z e : Cell n) (m : Marks) :
    let old := indicator (occupied x z e m)
    let k := deathsOn targets (eraseDest z e m a)
    indicator (occupied (next x a) z e m) + old*k =
      old + indicator (bornHere e a ∧ availPattern x z e m) + old*(k-1) := by
  classical
  dsimp only
  have upd := occupied_pattern_step x a good live z e m
  have none := no_deaths targets (eraseDest z e m a) all4
  have disj (o : occupied x z e m) (b : bornHere e a) : False := by
    cases a with
    | fail => exact b
    | virtual _ => exact b
    | real c => exact (choice_adm good (.real c) live) (b ▸ o.1)
  by_cases old : occupied x z e m <;> by_cases birth : bornHere e a ∧ availPattern x z e m
  · exact (disj old birth.1).elim
  · by_cases zero : deathsOn targets (eraseDest z e m a) = 0
    · simp [indicator,upd,old,birth,none.mp zero,zero]
    · have no : ¬(∀ j, ¬eraseDest z e m a j) := fun w => zero (none.mpr w)
      simp only [indicator,upd,old,birth,true_and,or_false,if_neg no,if_true,if_false,
        Nat.one_mul,Nat.zero_add,Nat.add_zero]; omega
  · simp [indicator,upd,old,birth]
  · simp [indicator,upd,old,birth]

theorem available_balance {n} (x : State n) (a : Choice n) (fresh : admissible x a)
    (z e : Cell n) (m : Marks) :
    let old := indicator (availPattern x z e m)
    let k := deathsOn allSlots (effect z e m a)
    indicator (availPattern (next x a) z e m) + old*k = old + old*(k-1) := by
  classical
  dsimp only
  have none := no_deaths allSlots (effect z e m a) all8
  have eq : deathsOn allSlots (effect z e m a) = 0 ↔
      (∀ i, ¬eraseOwn e a i) ∧ ∀ j, ¬eraseDest z e m a j := by
    rw [none]; exact ⟨fun h => ⟨fun i => h (.inl i),fun j => h (.inr j)⟩,
      fun h i => by cases i with | inl j => exact h.1 j | inr j => exact h.2 j⟩
  have upd := available_pattern_step x a fresh z e m
  by_cases old : availPattern x z e m <;> by_cases zero : deathsOn allSlots (effect z e m a) = 0 <;>
    simp [indicator,upd,old,← eq,zero] <;> omega

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.occupied_balance
#print axioms ArticuloA.Trayectoria.E2.available_balance
