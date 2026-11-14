import PresupuestoDePesos
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infix:50 " ≼ " => s.le

/-- One active physical line and one cell in a pre-step state. No
assumption in this theorem bounds a transition probability error. -/
theorem local_rates {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, a ≼ s.zero → a = s.zero)
    (j : Vertex) (e : Cell n) (live : j.2 < 2*n-1 ∧ x.active j.1 j.2)
    (v : Cell n → α) (a : α) (weight : ∀ i, weights s w.real (lines i) = a ⊗ v i)
    (sn : ns s n ≠ s.zero) (sq : ns s n ⊗ ns s n ≠ s.zero) (tm : timeMass s x ≠ s.zero)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero)
    (z c w₀ d₀ u₀ q₀ h₀ p piN eps off bal l M : α) :
    let size := ns s n
    let normal := norm s inv size
    let T := normal (timeMass s x)
    let Q := normal (ns s x.reals)
    let D := normal (auxDegree s x v j)
    let U := normal (Cart.part s x w j.1)
    let W := norm s inv (size ⊗ size) (boardSum s v (fun i => available x (lines i)))
    let u := w j.1 j.2
    let ke := inv (c ⊗ fourth s z) ⊗ piN
    let I := inv (l ⊗ l)
    let r := cost s I M eps
    let vErr := cost s I M (s.add eps off)
    T = c ⊗ z → T ≠ s.zero → c ⊗ fourth s z ≠ s.zero →
    l ⊗ l ≠ s.zero → l ≼ T → T ≼ M → z ≼ s.one → s.add (q₀ ⊗ z) (h₀ ⊗ z) = T →
    within s Q (q₀ ⊗ z) eps → within s D (d₀ ⊗ cube s z) eps →
    within s W (w₀ ⊗ fourth s z) eps → within s U (u₀ ⊗ z) eps →
    within s u₀ h₀ off → within s (s.add p u) s.one bal →
    s.add l eps ≼ (w₀ ⊗ fourth s z) → s.add l (s.add eps off) ≼ (h₀ ⊗ z) →
    w₀ ⊗ p = q₀ ⊗ d₀ → w₀ ⊗ piN = q₀ ⊗ v e →
    D ≼ M → u ≼ M → v e ≼ M → (q₀ ⊗ z) ≼ M → (h₀ ⊗ z) ≼ M →
    (inv T ⊗ p) ≼ M → (inv T ⊗ u) ≼ M → ke ≼ M →
    within s (size ⊗ realRate s x w inv j) (inv T ⊗ p) r ∧
    within s (size ⊗ virtRate s x w inv j) (inv T ⊗ u) vErr ∧
    within s (size ⊗ s.add (realRate s x w inv j) (virtRate s x w inv j)) (inv T)
      (s.add (s.add r vErr) (inv T ⊗ bal)) ∧
    within s ((size ⊗ size) ⊗ realAtom s x w inv e) ke r := by
  intro size normal T Q D U W u ke I r vErr ht hc hk hl low high zz init
    tq td tw tu offset balance wm um pdef edef dc uc vc qc hc₀ pc uv bc
  obtain ⟨rh,vh,bh⟩ := board_coordinates s x w inv recip v a weight sn sq tm rr vv j e live
  have result := tracked_step s inv recip proper T z c W D U Q (normal (ns s x.virtuals))
    w₀ d₀ u₀ q₀ h₀ p u (v e) piN _ _ _ eps off bal l M ht hc hk hl low high zz
    (colour_mass s x inv) init tq td tw tu offset balance wm um pdef edef rh vh bh dc uc vc qc hc₀ pc uv bc
  rw [s.mulAdd]
  exact result

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.local_rates
