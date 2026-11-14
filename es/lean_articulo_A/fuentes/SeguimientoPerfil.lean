import TasasNucleo
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊕ " => s.add
local infix:50 " ≼ " => s.le

/-- A uniform bound for a scaled rate if each primitive error is at most e. -/
def cost (I M e : α) := I ⊗ (((M ⊗ e) ⊕ (M ⊗ e)) ⊕ (M ⊗ (M ⊗ e)))

theorem up_left (a b : α) : a ≼ (a ⊕ b) := by
  have t := s.mono (s.refl a) (s.zero_le b)
  simpa [s.comm a s.zero,s.zero_add] using t

/-- Inputs: tracking four primitive observables, initial balance, scale
bounds, and the three cleared transition identities. No hazard error input. -/
theorem tracked_step (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (proper : ∀ a, a ≼ s.zero → a = s.zero)
    (T z c W D U Q H w₀ d₀ u₀ q₀ h₀ p u v piN R V B eps off bal l M : α)
    (time : T = c ⊗ z) (clock : T ≠ s.zero) (birthClock : c ⊗ fourth s z ≠ s.zero)
    (positive : l ⊗ l ≠ s.zero) (lower : l ≼ T) (upper : T ≼ M) (zle : z ≼ s.one)
    (mass : s.add Q H = T) (initial : s.add (q₀ ⊗ z) (h₀ ⊗ z) = T)
    (trQ : within s Q (q₀ ⊗ z) eps) (trD : within s D (d₀ ⊗ cube s z) eps)
    (trW : within s W (w₀ ⊗ fourth s z) eps) (trU : within s U (u₀ ⊗ z) eps)
    (offset : within s u₀ h₀ off) (balance : within s (p ⊕ u) s.one bal)
    (wsep : (l ⊕ eps) ≼ (w₀ ⊗ fourth s z))
    (usep : (l ⊕ (eps ⊕ off)) ≼ (h₀ ⊗ z))
    (pdef : w₀ ⊗ p = q₀ ⊗ d₀) (pidef : w₀ ⊗ piN = q₀ ⊗ v)
    (realId : (T ⊗ W) ⊗ R = Q ⊗ D) (virtId : (T ⊗ U) ⊗ V = H ⊗ u)
    (birthId : (T ⊗ W) ⊗ B = Q ⊗ v)
    (dc : D ≼ M) (uc : u ≼ M) (vc : v ≼ M)
    (qc : (q₀ ⊗ z) ≼ M) (hc : (h₀ ⊗ z) ≼ M)
    (pc : (inv T ⊗ p) ≼ M) (uvc : (inv T ⊗ u) ≼ M)
    (bc : (inv (c ⊗ fourth s z) ⊗ piN) ≼ M) :
    let I := inv (l ⊗ l)
    let r := cost s I M eps
    let vErr := cost s I M (eps ⊕ off)
    within s R (inv T ⊗ p) r ∧
    within s V (inv T ⊗ u) vErr ∧
    within s (R ⊕ V) (inv T) ((r ⊕ vErr) ⊕ (inv T ⊗ bal)) ∧
    within s B (inv (c ⊗ fourth s z) ⊗ piN) r := by
  dsimp only
  have ea := up_left s eps off
  have complementQ := grow s (complement s mass initial trQ) ea
  have uz := scale s z offset
  rw [s.mulComm z u₀,s.mulComm z h₀] at uz
  have offset' := s.mulMono zle (s.refl off)
  rw [s.oneMul] at offset'
  have track := within_chain s trU (grow s uz offset')
  obtain ⟨wr,wi⟩ := denominator s inv recip proper positive lower trW wsep
  obtain ⟨ur,ui⟩ := denominator s inv recip proper positive lower track usep
  have hr := rate_bound s inv recip wr wi realId (ideal_real s inv recip clock pdef)
    trQ trD trW dc qc pc upper
  have hv := rate_bound s inv recip ur ui virtId (ideal_virtual s inv recip clock)
    complementQ (within_self s u (eps ⊕ off)) track uc hc uvc upper
  have bref := ideal_birth s inv recip birthClock pidef
  rw [←time] at bref
  have hb := rate_bound s inv recip wr wi birthId bref trQ (within_self s v eps) trW vc qc bc upper
  have joined := within_add s hr hv
  have target := scale s (inv T) balance
  rw [s.mulAdd,s.mulOne] at target
  exact ⟨hr,hv,within_chain s joined target,hb⟩

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.tracked_step
