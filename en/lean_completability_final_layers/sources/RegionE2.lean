import GeneradorEnRegion
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type}
abbrev activeLine {n} (x : State n) (j : Vertex) := j.2 < 2*n-1 ∧ x.active j.1 j.2 = true

/-- One stopped, pre-step state. Only scalar profile data, finite
quadrature errors and the four trajectory errors enter this interface. -/
structure Region {n} (s : ProfileScale α) (x : State n) (w : ColorWeights α) (inv : α → α) where
  v : Cell n → α
  common : α
  z : α
  c : α
  w₀ : α
  d₀ : Vertex → α
  u₀ : Fin 4 → α
  q₀ : α
  h₀ : α
  p : Vertex → α
  piN : Cell n → α
  eps : α
  off : α
  bal : α
  l : α
  M : α
  mr : α
  mv : α
  wt : ∀ e, weights s w.real (lines e) = s.mul common (v e)
  sizePos : ns s n ≠ s.zero
  commonPos : common ≠ s.zero
  floorPos : l ≠ s.zero
  running : timeMass s x ≠ s.zero
  clock : norm s inv (ns s n) (timeMass s x) = s.mul c z
  clockPos : s.mul c z ≠ s.zero
  sourceClock : s.mul c (fourth s z) ≠ s.zero
  low : s.le l (s.mul c z)
  high : s.le (s.mul c z) M
  clockFrac : s.le z s.one
  initial : s.add (s.mul q₀ z) (s.mul h₀ z) = s.mul c z
  trackQ : within s (norm s inv (ns s n) (ns s x.reals)) (s.mul q₀ z) eps
  trackD : ∀ j, activeLine x j → within s (norm s inv (ns s n) (auxDegree s x v j)) (s.mul (d₀ j) (cube s z)) eps
  trackW : within s (norm s inv (s.mul (ns s n) (ns s n)) (boardSum s v (fun e => available x (lines e))))
    (s.mul w₀ (fourth s z)) eps
  trackU : ∀ f, within s (norm s inv (ns s n) (Cart.part s x w f)) (s.mul (u₀ f) z) eps
  offset : ∀ f, within s (u₀ f) h₀ off
  balance : ∀ j, activeLine x j → within s (s.add (p j) (w j.1 j.2)) s.one bal
  wMargin : s.le (s.add l eps) (s.mul w₀ (fourth s z))
  uMargin : s.le (s.add l (s.add eps off)) (s.mul h₀ z)
  load : ∀ j, s.mul w₀ (p j) = s.mul q₀ (d₀ j)
  cellLoad : ∀ e, s.mul w₀ (piN e) = s.mul q₀ (v e)
  degreeMax : ∀ j, activeLine x j → s.le (norm s inv (ns s n) (auxDegree s x v j)) M
  weightMax : ∀ e, s.le (v e) mr
  cellMax : s.le mr M
  tupleMax : ∀ g ∈ virtualEdges (2*n-1), available x g → s.le (weights s w g) mv
  vertexMax : ∀ j, activeLine x j → s.le (w j.1 j.2) M
  qMax : s.le (s.mul q₀ z) M
  hMax : s.le (s.mul h₀ z) M
  pMax : ∀ j, activeLine x j → s.le (s.mul (inv (s.mul c z)) (p j)) M
  uMax : ∀ j, activeLine x j → s.le (s.mul (inv (s.mul c z)) (w j.1 j.2)) M
  piMax : ∀ e, s.le (s.mul (inv (s.mul c (fourth s z))) (piN e)) M

namespace Region
variable {n} {s : ProfileScale α} {x : State n} {w : ColorWeights α} {inv : α → α}
variable (A : Region s x w inv)
local infixl:70 " ⊗ " => s.mul
abbrev time := A.c ⊗ A.z
abbrev budget := cost s (inv (A.l ⊗ A.l)) A.M A.eps
abbrev vBudget := cost s (inv (A.l ⊗ A.l)) A.M (s.add A.eps A.off)
abbrev combined := s.add (s.add A.budget A.vBudget) (inv A.time ⊗ A.bal)
abbrev birth (e : Cell n) := inv (A.c ⊗ fourth s A.z) ⊗ A.piN e

theorem raw_floors (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero) :
    s.le (((ns s n ⊗ ns s n) ⊗ A.common) ⊗ A.l) (total s (realChoices s x w)) ∧
    (∀ f, s.le (ns s n ⊗ A.l) (Cart.part s x w f)) ∧
    total s (realChoices s x w) ≠ s.zero ∧ total s (virtualChoices s x w) ≠ s.zero := by
  apply positive_rows s x w inv recip proper A.v A.common A.l A.wt A.sizePos A.commonPos A.floorPos
    (margin s A.trackW A.wMargin)
  intro f
  have scaled := scale s A.z (A.offset f)
  rw [s.mulComm A.z (A.u₀ f),s.mulComm A.z A.h₀] at scaled
  have shrink := s.mulMono A.clockFrac (s.refl A.off)
  rw [s.oneMul] at shrink
  exact margin s (within_chain s (A.trackU f) (grow s scaled shrink)) A.uMargin

theorem estimates (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero)
    (j : Vertex) (live : activeLine x j) (e : Cell n) :
    within s (ns s n ⊗ realRate s x w inv j) (inv A.time ⊗ A.p j) A.budget ∧
    within s (ns s n ⊗ virtRate s x w inv j) (inv A.time ⊗ w j.1 j.2) A.vBudget ∧
    within s (ns s n ⊗ s.add (realRate s x w inv j) (virtRate s x w inv j)) (inv A.time) A.combined ∧
    within s ((ns s n ⊗ ns s n) ⊗ realAtom s x w inv e) (A.birth e) A.budget := by
  obtain ⟨_,_,rr,vv⟩ := A.raw_floors recip proper
  have h := local_rates s x w inv recip proper j e live A.v A.common A.wt A.sizePos
    (mul_live s inv recip A.sizePos A.sizePos) A.running rr vv A.z A.c A.w₀ (A.d₀ j)
    (A.u₀ j.1) A.q₀ A.h₀ (A.p j) (A.piN e) A.eps A.off A.bal A.l A.M
  dsimp only at h; rw [A.clock] at h
  exact h rfl A.clockPos A.sourceClock (mul_live s inv recip A.floorPos A.floorPos) A.low A.high A.clockFrac A.initial
    A.trackQ (A.trackD j live) A.trackW (A.trackU j.1) (A.offset j.1) (A.balance j live)
    A.wMargin A.uMargin (A.load j) (A.cellLoad e) (A.degreeMax j live) (A.vertexMax j live)
    (s.trans (A.weightMax e) A.cellMax) A.qMax A.hMax (A.pMax j live) (A.uMax j live) (A.piMax e)

end Region
end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.Region.estimates
