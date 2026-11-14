import ErrorDeTrayectoria
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul

open Classical in
/-- Handoff from the scaled estimates of local_rates to the two finite
one-step inequalities, with the original choices of both colours. -/
theorem local_generator {n} (x : State n) (good : coherent x)
    (w : ColorWeights α) (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (atoms : AtomBounds s x w inv) (z e : Cell n) (m : Marks) (T born er eb vr balance : α)
    (p : Vertex → α) (sn : ns s n ≠ s.zero)
    (hReal : ∀ v : Vertex, v.2 < 2*n-1 ∧ x.active v.1 v.2 →
      within s (ns s n ⊗ realRate s x w inv v) (inv T ⊗ p v) er)
    (hActive : ∀ v : Vertex, v.2 < 2*n-1 ∧ x.active v.1 v.2 →
      within s (ns s n ⊗ s.add (realRate s x w inv v) (virtRate s x w inv v)) (inv T)
        (s.add (s.add er vr) (inv T ⊗ balance)))
    (hBirth : availPattern x z e m →
      within s ((ns s n ⊗ ns s n) ⊗ realAtom s x w inv e) born eb) :
    let size := ns s n
    let b := inv size ⊗ s.add (s.add er vr) (inv T ⊗ balance)
    let d := inv (size ⊗ size) ⊗ eb
    let ke := inv (size ⊗ size) ⊗ born
    let rate := referenceRate (inv size ⊗ inv T) (fun j => inv size ⊗ (inv T ⊗ p (side j,key z e j))) m
    let row := choices s x w inv
    let present := fun occ => meanN s row (fun _ => indicator (pattern occ x z e m))
    let future := fun occ => meanN s row (fun a => indicator (pattern occ (next x a) z e m))
    let loss := fun occ => weightedSingles s occ x z e m rate
    within s (s.add (future true) (loss true))
      (s.add (present true) (if availPattern x z e m then ke else s.zero))
      (s.add (s.times 4 (if occupied x z e m then b else s.zero))
        (s.add (if availPattern x z e m then d else s.zero)
          (s.times (indicator (occupied x z e m)*6) atoms.pairCap))) ∧
    within s (s.add (future false) (loss false)) (present false)
      (s.add (s.times 8 b) (s.times (indicator (availPattern x z e m)*28) atoms.pairCap)) := by
  have cap := s.trans (up_left s er vr) (up_left s (s.add er vr) (inv T ⊗ balance))
  obtain ⟨rates,birth⟩ := generator_inputs s x w inv recip atoms.realNormal atoms.virtualNormal
    z e m (ns s n) T born er eb _ p sn (mul_live s inv recip sn sn) cap hReal hActive hBirth
  exact ⟨occupied_generator s x good w inv atoms z e m _ _ _ _ _ (rates true) birth,
    available_generator s x good w inv atoms z e m _ _ _ (rates false)⟩

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.local_generator
