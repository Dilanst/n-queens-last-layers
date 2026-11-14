import ErrorMedio
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

noncomputable def measured {n} (x : State n) (u : ColorWeights α) (inv : α → α) (z e : Cell n) (m : Marks)
    (i : Both) := meanN s (choices s x u inv) (fun a => indicator (singled z e m i a))
def referenceRate (alpha : α) (beta : Fin 4 → α) (m : Marks) : Both → α
  | .inl _ => alpha
  | .inr j => if m j then alpha else beta j

theorem guarded_old {n} (occ : Bool) (x : State n) (good : coherent x) (z e : Cell n)
    (m : Marks) (i : Both) (h : guardP occ x z e m i) : pattern occ x z e m := by
  cases i with
  | inl _ => exact h
  | inr j =>
    cases occ with
    | true => exact ⟨h.1,h.2.1,((promoted x good z e m j).mp h.2.2).1⟩
    | false => exact ⟨h.1,h.2.1,((promoted x good z e m j).mp h.2.2).1⟩

open Classical in
theorem occupied_generator {n} (x : State n) (good : coherent x) (u : ColorWeights α)
    (inv : α → α) (B : AtomBounds s x u inv) (z e : Cell n) (m : Marks)
    (alpha : α) (beta : Fin 4 → α) (ke b d : α)
    (rates : ∀ i ∈ lossKeys true, guardP true x z e m i →
      within s (measured s x u inv z e m i) (referenceRate alpha beta m i) b)
    (source : availPattern x z e m → within s (realAtom s x u inv e) ke d) :
    let row := choices s x u inv
    let past := meanN s row (fun _ => indicator (occupied x z e m))
    let future := meanN s row (fun a => indicator (occupied (next x a) z e m))
    let loss := weightedSingles s true x z e m (referenceRate alpha beta m)
    let birth := if availPattern x z e m then ke else s.zero
    within s (s.add future loss) (s.add past birth)
      (s.add (s.times 4 (if occupied x z e m then b else s.zero)) (s.add (if availPattern x z e m then d else s.zero)
        (s.times (indicator (occupied x z e m)*6) B.pairCap))) := by
  classical
  dsimp only
  have eq := occupied_mean s x u inv z e m good
  dsimp only at eq
  rw [birth_mass s x u inv B.realNormal B.virtualNormal] at eq
  have singles := exact_singles s true x good u inv z e m
  simp only [pattern,lossKeys,if_true,deathsOn,List.countP_map,Function.comp_def,effect] at singles
  change meanN s _ (fun a => indicator (occupied x z e m)*deathsOn targets (eraseDest z e m a)) = _ at singles
  rw [singles] at eq
  have supported := singles_error s true x z e m (measured s x u inv z e m) (referenceRate alpha beta m)
    (if occupied x z e m then b else s.zero) (by
      intro i hi guard; have old : occupied x z e m := guarded_old true x good z e m i guard
      simpa only [if_pos old] using rates i hi guard)
  apply compare_balance s eq supported _ (losses_supported s x u inv z e m B).1
  by_cases a : availPattern x z e m
  · simpa [a] using source a
  · simpa [a] using within_self s s.zero s.zero

theorem available_generator {n} (x : State n) (good : coherent x) (u : ColorWeights α)
    (inv : α → α) (B : AtomBounds s x u inv) (z e : Cell n) (m : Marks)
    (alpha : α) (beta : Fin 4 → α) (b : α)
    (rates : ∀ i ∈ lossKeys false, guardP false x z e m i →
      within s (measured s x u inv z e m i) (referenceRate alpha beta m i) b) :
    let row := choices s x u inv
    let past := meanN s row (fun _ => indicator (availPattern x z e m))
    let future := meanN s row (fun a => indicator (availPattern (next x a) z e m))
    let loss := weightedSingles s false x z e m (referenceRate alpha beta m)
    within s (s.add future loss) past
      (s.add (s.times 8 b) (s.times (indicator (availPattern x z e m)*28) B.pairCap)) := by
  dsimp only
  have eq := available_mean s x u inv z e m good
  dsimp only at eq
  have singles := exact_singles s false x good u inv z e m
  change meanN s _ (fun a => indicator (availPattern x z e m)*deathsOn allSlots (effect z e m a)) = _ at singles
  rw [singles] at eq
  have zero (v : α) : s.add v s.zero = v := by rw [s.comm,s.zero_add]
  have eq' := eq
  rw [← zero (meanN s (choices s x u inv) (fun _ => indicator (availPattern x z e m)))] at eq'
  have est := compare_balance s eq' (singles_error s false x z e m _ _ b rates)
    (within_self s s.zero s.zero) (losses_supported s x u inv z e m B).2
  simpa only [zero,s.zero_add] using est

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.occupied_generator
#print axioms ArticuloA.Trayectoria.E2.available_generator
