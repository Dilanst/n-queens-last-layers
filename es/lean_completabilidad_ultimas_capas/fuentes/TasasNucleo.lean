import BlancosE2
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem clock_quota (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size T Q raw count : α} (sn : size ≠ s.zero) (rn : raw ≠ s.zero)
    (clock : size ⊗ T = raw) (pieces : size ⊗ Q = count) :
    T ⊗ (inv raw ⊗ count) = Q := by
  calc
    _ = (inv size ⊗ size) ⊗ (T ⊗ (inv raw ⊗ count)) := by rw [recip _ sn,s.oneMul]
    _ = (inv raw ⊗ (size ⊗ T)) ⊗ (inv size ⊗ count) := by ac_rfl
    _ = _ := by rw [clock,recip _ rn,s.oneMul,←pieces,←s.mulAssoc,recip _ sn,s.oneMul]

/-- Applies also when the original real weights have a common factor x_*². -/
theorem real_kernel_scaled (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {T W Q D quota raw g scale factor : α} (live : raw ≠ s.zero)
    (time : T ⊗ quota = Q) (mass : (scale ⊗ factor) ⊗ W = raw) (piece : factor ⊗ D = g) :
    (T ⊗ W) ⊗ (scale ⊗ (quota ⊗ (inv raw ⊗ g))) = Q ⊗ D := by
  rw [←piece]
  calc
    _ = (T ⊗ quota) ⊗ ((inv raw ⊗ ((scale ⊗ factor) ⊗ W)) ⊗ D) := by ac_rfl
    _ = _ := by rw [time,mass,recip _ live,s.oneMul]

theorem virtual_kernel_scaled {T U H size raw rate quota u : α}
    (time : T ⊗ quota = H) (mass : size ⊗ U = raw) (line : rate ⊗ raw = quota ⊗ u) :
    (T ⊗ U) ⊗ (size ⊗ rate) = H ⊗ u := by
  calc
    _ = T ⊗ (rate ⊗ (size ⊗ U)) := by ac_rfl
    _ = _ := by rw [mass,line,←s.mulAssoc,time]

/-- The three identities have the actual transition probabilities as outputs. -/
theorem kernel_coordinates {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (v : Vertex) (e : Cell n)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero)
    (active : v.2 < 2*n-1 ∧ x.active v.1 v.2)
    (size T W U Q H D weight a : α)
    (rclock : T ⊗ quota s x inv x.reals = Q) (vclock : T ⊗ quota s x inv x.virtuals = H)
    (rnormal : ((size ⊗ size) ⊗ a) ⊗ W = total s (realChoices s x w))
    (degree : (size ⊗ a) ⊗ D = realDegree s x w v)
    (cell : a ⊗ weight = weights s w.real (lines e)) (family : size ⊗ U = Cart.part s x w v.1) :
    (T ⊗ W) ⊗ (size ⊗ realRate s x w inv v) = Q ⊗ D ∧
    (T ⊗ U) ⊗ (size ⊗ virtRate s x w inv v) = H ⊗ w v.1 v.2 ∧
    (T ⊗ W) ⊗ ((size ⊗ size) ⊗ realAtom s x w inv e) = Q ⊗ weight := by
  refine ⟨?_,?_,?_⟩
  · apply real_kernel_scaled s inv recip rr rclock _ degree
    rwa [←s.mulAssoc size size a]
  · apply virtual_kernel_scaled s vclock family
    simpa only [if_pos active] using virt_rate_cleared s x w inv recip vv v
  · exact real_kernel_scaled s inv recip rr rclock rnormal cell

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.kernel_coordinates
