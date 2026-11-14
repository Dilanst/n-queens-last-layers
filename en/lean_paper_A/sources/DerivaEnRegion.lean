import RegionE2
namespace ArticuloA.Trayectoria.E2.Regular.Region
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {n α} {s : ProfileScale α} {x : State n} {w : ColorWeights α} {inv : α → α}
local infixl:70 " ⊗ " => s.mul

open Classical in
/-- Conditional on the primitive region at the current state.
The same atom budget is used in the occupied and available comparisons. -/
theorem pattern_drift (A : Region s x w inv) (good : coherent x)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero)
    (z e : Cell n) (m : Marks) :
    let size := ns s n
    let b := inv size ⊗ A.combined
    let d := inv (size ⊗ size) ⊗ A.budget
    let rate := referenceRate (inv size ⊗ inv A.time)
      (fun j => inv size ⊗ (inv A.time ⊗ A.p (side j,key z e j))) m
    let ke := inv (size ⊗ size) ⊗ A.birth e
    let row := choices s x w inv
    let present := fun occ => meanN s row (fun _ => indicator (pattern occ x z e m))
    let future := fun occ => meanN s row (fun i => indicator (pattern occ (next x i) z e m))
    let loss := fun occ => weightedSingles s occ x z e m rate
    ∃ Pstar : α,
      s.le (s.times (n*n) Pstar) (s.add (inv A.l ⊗ A.mr) (s.times 4 (inv (s.four (fun _ => A.l)) ⊗ A.mv))) ∧
      within s (s.add (future true) (loss true)) (s.add (present true) (if availPattern x z e m then ke else s.zero))
        (s.add (s.times 4 (if occupied x z e m then b else s.zero))
          (s.add (if availPattern x z e m then d else s.zero) (s.times (indicator (occupied x z e m)*6) Pstar))) ∧
      within s (s.add (future false) (loss false)) (present false)
        (s.add (s.times 8 b) (s.times (indicator (availPattern x z e m)*28) Pstar)) := by
  obtain ⟨realMin,virtMin,rr,vv⟩ := A.raw_floors recip proper
  have raw (i : Cell n) (_ : available x (lines i) = true) :
      s.le (weights s w.real (lines i)) (A.common ⊗ A.mr) := by
    rw [A.wt]; exact s.mulMono (s.refl _) (A.weightMax i)
  have live2 := mul_live s inv recip A.floorPos A.floorPos
  have live4 : s.four (fun _ => A.l) ≠ s.zero := mul_live s inv recip live2 live2
  let atom := fromWeights s x w inv rr vv (A.common ⊗ A.mr) A.mv raw A.tupleMax
  refine ⟨atom.pairCap,pair_from_margins s x w inv recip rr vv A.running A.l A.common
    A.mr A.mv A.floorPos live4 realMin virtMin raw A.tupleMax,?_⟩
  apply local_generator s x good w inv recip atom z e m A.time (A.birth e) A.budget A.budget A.vBudget A.bal A.p A.sizePos
  · exact fun j hj => (A.estimates recip proper j hj e).1
  · exact fun j hj => (A.estimates recip proper j hj e).2.2.1
  · intro av
    have on : activeLine x (0,lines e 0) :=
      ⟨on_board e 0, List.all_eq_true.mp av.2.1 0 (by simp [List.finRange,List.mem_ofFn])⟩
    exact (A.estimates recip proper _ on e).2.2.2

end ArticuloA.Trayectoria.E2.Regular.Region
#print axioms ArticuloA.Trayectoria.E2.Regular.Region.pattern_drift
