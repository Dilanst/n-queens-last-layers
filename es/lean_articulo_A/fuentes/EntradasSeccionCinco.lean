import LineasGuardadas
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊕ " => s.add

theorem drop_scale (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size a target err : α} (positive : size ≠ s.zero)
    (bound : within s (size ⊗ a) target err) :
    within s a (inv size ⊗ target) (inv size ⊗ err) := by
  have v := scale s (inv size) bound
  rwa [←s.mulAssoc,recip _ positive,s.oneMul] at v

/-- Consume the scaled estimates on active lines. This proves precisely
the rates and source hypotheses of the two local generators. -/
theorem generator_inputs {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero)
    (z e : Cell n) (m : Marks) (size T born er eb allErr : α) (p : Vertex → α)
    (sn : size ≠ s.zero) (sq : size ⊗ size ≠ s.zero) (weak : s.le er allErr)
    (realLine : ∀ v : Vertex, v.2 < 2*n-1 ∧ x.active v.1 v.2 →
      within s (size ⊗ realRate s x w inv v) (inv T ⊗ p v) er)
    (jointLine : ∀ v : Vertex, v.2 < 2*n-1 ∧ x.active v.1 v.2 →
      within s (size ⊗ (s.add (realRate s x w inv v) (virtRate s x w inv v))) (inv T) allErr)
    (newborn : availPattern x z e m → within s ((size ⊗ size) ⊗ realAtom s x w inv e) born eb) :
    (∀ occ i, i ∈ lossKeys occ → guardP occ x z e m i →
      within s (measured s x w inv z e m i)
        (referenceRate (inv size ⊗ inv T) (fun j => inv size ⊗ (inv T ⊗ p (side j,key z e j))) m i)
        (inv size ⊗ allErr)) ∧
    (availPattern x z e m → within s (realAtom s x w inv e)
      (inv (size ⊗ size) ⊗ born) (inv (size ⊗ size) ⊗ eb)) := by
  refine ⟨?_,fun avail => drop_scale s inv recip sq (newborn avail)⟩
  intro occ i hi guard
  have on := guarded_active occ x z e m i hi guard
  have add := drop_scale s inv recip sn (jointLine _ on)
  have real := drop_scale s inv recip sn (grow s (realLine _ on) weak)
  rw [measured_rate s x w inv rr vv]
  cases i with
  | inl j => exact add
  | inr j =>
    rw [target_vertex] at real add ⊢
    cases mj : m j <;> simp [bothColours,referenceRate,mj] <;> first | exact add | exact real

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.generator_inputs
