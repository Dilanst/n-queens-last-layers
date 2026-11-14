import PerdidaDeFamilia
namespace ArticuloA.Trayectoria.E2.Regular.Region
open ArticuloA ArticuloA.Corte ProfileKernel
variable {n α} {s : ProfileScale α} {x : State n} {w : ColorWeights α} {inv : α → α}
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

private theorem weighted_sum (L : List Nat) (mass rate : Nat → α) (a b : α)
    (est : ∀ j ∈ L, within s (mass j ⊗ rate j) (mass j ⊗ a) (mass j ⊗ b)) :
    within s (s.sum L (fun j => mass j ⊗ rate j)) (s.sum L mass ⊗ a) (s.sum L mass ⊗ b) := by
  rw [←Cart.sum_scale,←Cart.sum_scale]
  induction L with
  | nil => exact within_self s _ _
  | cons i L ih =>
    exact within_add s (est i (by simp)) (ih (fun j hj => est j (by simp [hj])))

theorem family_drift (A : Region s x w inv) (f : Fin 4)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero) :
    let U := Cart.part s x w f
    let a := inv (ns s n) ⊗ inv A.time
    let b := inv (ns s n) ⊗ A.combined
    within s (avg s (choices s x w inv) (lostWeight s x w f)) (U ⊗ a) (U ⊗ b) := by
  intro U a b
  obtain ⟨_,_,rr,vv⟩ := A.raw_floors recip proper
  rw [family_rate s x w inv f rr vv]
  let mass := fun j => if x.active f j then w f j else s.zero
  let rate := fun j => realRate s x w inv (f,j) ⊞ virtRate s x w inv (f,j)
  have zero (v : α) : s.zero ⊗ v = s.zero := by rw [s.mulComm,s.mulZero]
  have term (j : Nat) : (if x.active f j then w f j ⊗ rate j else s.zero) = mass j ⊗ rate j := by
    cases h : x.active f j <;> simp [mass,h,zero]
  change within s (s.sum _ (fun j => if x.active f j then w f j ⊗ rate j else s.zero)) _ _
  rw [funext term]
  apply weighted_sum _ mass rate a b
  intro j hj
  cases h : x.active f j with
  | false => simpa [mass,h,zero] using within_self s s.zero s.zero
  | true =>
    have ix := List.mem_range.mp hj
    have nonempty : 0<n := by omega
    let cell : Cell n := (⟨0,nonempty⟩,⟨0,nonempty⟩)
    have line := (A.estimates recip proper (f,j) ⟨ix,h⟩ cell).2.2.1
    exact scale s (mass j) (drop_scale s inv recip A.sizePos line)

end ArticuloA.Trayectoria.E2.Regular.Region
#print axioms ArticuloA.Trayectoria.E2.Regular.Region.family_drift
