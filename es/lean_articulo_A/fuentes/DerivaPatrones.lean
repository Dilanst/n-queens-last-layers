import RestoPares
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

theorem row_allowed {n α} (s : ProfileScale α) (x : State n) (u : ColorWeights α) (inv : α → α)
    (a : α × Choice n) (mem : a ∈ choices s x u inv) : allowed x a.2 := by
  classical
  have chosen {L : Atoms α (Choice n)} (yes : ∀ j ∈ L, allowed x j.2)
      (j : α × Choice n) (hj : j ∈ choose s L .fail inv) : allowed x j.2 := by
    unfold choose at hj; split at hj
    · obtain rfl := List.mem_singleton.mp hj; trivial
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hj; exact yes k hk
  rcases List.mem_append.mp mem with r|v
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp r
    exact chosen (by intro i hi; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi; exact (List.mem_filter.mp he).2) j hj
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp v
    exact chosen (by intro i hi; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hi; exact (List.mem_filter.mp he).2) j hj

section
variable {α : Type} (s : ProfileScale α) {n : Nat} (x : State n) (u : ColorWeights α)
    (inv : α → α) (z e : Cell n) (m : Marks)
local notation "row" => choices s x u inv

/-- Conditional first-moment identities, on the unconditioned row of choices.
The old bit is inside the expectations to retain the support of the remainder. -/
theorem occupied_mean (good : coherent x) :
    let old := indicator (occupied x z e m)
    let k := fun a => deathsOn targets (eraseDest z e m a)
    s.add (meanN s row (fun a => indicator (occupied (next x a) z e m))) (meanN s row (fun a => old*k a)) =
    s.add (s.add (meanN s row (fun _ => old))
      (meanN s row (fun a => indicator (bornHere e a ∧ availPattern x z e m))))
      (meanN s row (fun a => old*(k a-1))) := by
  dsimp only
  rw [← mean_plus,← mean_plus,← mean_plus]
  exact mean_eq s _ _ _ (fun a ha => occupied_balance x a.2 good (row_allowed s x u inv a ha) z e m)

theorem available_mean (good : coherent x) :
    let old := indicator (availPattern x z e m)
    let k := fun a => deathsOn allSlots (effect z e m a)
    s.add (meanN s row (fun a => indicator (availPattern (next x a) z e m))) (meanN s row (fun a => old*k a)) =
      s.add (meanN s row (fun _ => old)) (meanN s row (fun a => old*(k a-1))) := by
  dsimp only
  rw [← mean_plus,← mean_plus]
  exact mean_eq s _ _ _ (fun a ha => available_balance x a.2 (choice_adm good _ (row_allowed s x u inv a ha)) z e m)

/-- Concrete overlap bounds, retaining zero error if the old pattern is absent. -/
theorem losses_supported (B : AtomBounds s x u inv) :
    s.le (meanN s row (fun a => indicator (occupied x z e m)*(deathsOn targets (eraseDest z e m a)-1)))
      (s.times (indicator (occupied x z e m)*6) B.pairCap) ∧
    s.le (meanN s row (fun a => indicator (availPattern x z e m)*(deathsOn allSlots (effect z e m a)-1)))
      (s.times (indicator (availPattern x z e m)*28) B.pairCap) := by
  classical
  constructor
  · by_cases h : occupied x z e m
    · simpa [indicator,h] using B.four_excess z e h.2.1 m
    · simp [indicator,h,mean_zero,MassScale.times,s.refl]
  · by_cases h : availPattern x z e m
    · simpa [indicator,h] using B.eight_excess z e h.1 m
    · simp [indicator,h,mean_zero,MassScale.times,s.refl]

end
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.occupied_mean
#print axioms ArticuloA.Trayectoria.E2.available_mean
#print axioms ArticuloA.Trayectoria.E2.losses_supported
