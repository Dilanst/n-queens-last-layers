import PasoOriginal
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊕ " => s.add
local infix:50 " ≼ " => s.le

theorem grow {x y a b : α} (h : within s x y a) (ab : a ≼ b) : within s x y b :=
  ⟨s.trans h.1 (s.mono (s.refl _) ab), s.trans h.2 (s.mono (s.refl _) ab)⟩

theorem scale (t : α) {x y e : α} (h : within s x y e) :
    within s (t ⊗ x) (t ⊗ y) (t ⊗ e) := by
  have a := s.mulMono (s.refl t) h.1
  have b := s.mulMono (s.refl t) h.2
  rw [s.mulAdd] at a b
  exact ⟨a,b⟩

theorem product_error {q q₀ d d₀ e a : α} (hq : within s q q₀ e) (hd : within s d d₀ a) :
    within s (q ⊗ d) (q₀ ⊗ d₀) ((d ⊗ e) ⊕ (q₀ ⊗ a)) := by
  have v := scale s d hq
  rw [s.mulComm d q,s.mulComm d q₀] at v
  exact within_chain s v (scale s q₀ hd)

theorem quotient_error (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {y y₀ W W₀ A A₀ e a : α} (live : W ≠ s.zero)
    (actual : W ⊗ y = A) (ideal : W₀ ⊗ y₀ = A₀)
    (num : within s A A₀ e) (den : within s W W₀ a) :
    within s y y₀ (inv W ⊗ (e ⊕ (y₀ ⊗ a))) := by
  have adjust := scale s y₀ (show within s W₀ W a from ⟨den.2,den.1⟩)
  rw [s.mulComm y₀ W₀,ideal,s.mulComm y₀ W] at adjust
  have est := within_chain s num adjust
  rw [←actual] at est
  have res := scale s (inv W) est
  simpa only [←s.mulAssoc,recip W live,s.oneMul] using res

theorem inv_antitone (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {a b : α} (aLive : a ≠ s.zero) (bLive : b ≠ s.zero) (ab : a ≼ b) : inv b ≼ inv a := by
  have t := s.mulMono (s.refl (inv a)) ab
  rw [recip a aLive] at t
  have u := s.mulMono t (s.refl (inv b))
  rwa [s.oneMul,s.mulAssoc,s.mulComm b (inv b),recip b bLive,s.mulOne] at u

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.quotient_error
