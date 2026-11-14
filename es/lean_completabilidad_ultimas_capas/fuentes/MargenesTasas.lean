import CocientesRegulares
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊕ " => s.add
local infix:50 " ≼ " => s.le

theorem margin {W W₀ e l : α} (track : within s W W₀ e) (sep : (l ⊕ e) ≼ W₀) : l ≼ W :=
  s.cancel (s.trans sep track.2)

theorem nonzero_of_lower (proper : ∀ a, a ≼ s.zero → a = s.zero)
    {l w : α} (live : l ≠ s.zero) (lower : l ≼ w) : w ≠ s.zero := by
  intro h; rw [h] at lower; exact live (proper l lower)

/-- A common lower bound l is imposed on T and on the tracked normalizer,
via its ideal margin; the error on T is zero. -/
theorem denominator (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (proper : ∀ a, a ≼ s.zero → a = s.zero)
    {T W W₀ e l : α} (pos : l ⊗ l ≠ s.zero) (clock : l ≼ T)
    (track : within s W W₀ e) (sep : (l ⊕ e) ≼ W₀) :
    T ⊗ W ≠ s.zero ∧ inv (T ⊗ W) ≼ inv (l ⊗ l) := by
  have low := s.mulMono clock (margin s track sep)
  have nz := nonzero_of_lower s proper pos low
  exact ⟨nz,inv_antitone s inv recip pos nz low⟩

/-- Explicit perturbation estimate for a rate with numerator q*d and
denominator T*W; T is exact. -/
theorem rate_bound (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {q q₀ d d₀ W W₀ T y y₀ eq ed ew D Q Y M I : α}
    (live : T ⊗ W ≠ s.zero) (cap : inv (T ⊗ W) ≼ I)
    (now : (T ⊗ W) ⊗ y = q ⊗ d) (ref : (T ⊗ W₀) ⊗ y₀ = q₀ ⊗ d₀)
    (tq : within s q q₀ eq) (td : within s d d₀ ed) (tw : within s W W₀ ew)
    (dc : d ≼ D) (qc : q₀ ≼ Q) (yc : y₀ ≼ Y) (tc : T ≼ M) :
    within s y y₀ (I ⊗ (((D ⊗ eq) ⊕ (Q ⊗ ed)) ⊕ (Y ⊗ (M ⊗ ew)))) := by
  have raw := quotient_error s inv recip live now ref (product_error s tq td) (scale s T tw)
  exact grow s raw (s.mulMono cap
    (s.mono (s.mono (s.mulMono dc (s.refl _)) (s.mulMono qc (s.refl _)))
      (s.mulMono yc (s.mulMono tc (s.refl _)))))

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.rate_bound
