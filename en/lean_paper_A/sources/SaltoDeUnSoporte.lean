import DerivaPorRaizE2
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

def gated (L : List ι) (gate : ι → Bool) (w : ι → α) :=
  s.sum L (fun i => if gate i then w i else s.zero)

theorem between_zero {x b : α} (h : s.le x b) : within s x s.zero b :=
  ⟨by simpa only [s.zero_add] using h,s.zero_le _⟩

/-- First change the support at new weights, then the weights on the old support. -/
theorem support_jump (L : List ι) (old new : ι → Bool) (c C : ι → α) (cap shift : α)
    (bounded : ∀ i, s.le (C i) cap) (drift : ∀ i, within s (C i) (c i) shift) :
    within s (gated s L new C) (gated s L old c)
      (s.times (L.countP (fun i => old i != new i)) cap ⊞ s.times (L.countP old) shift) := by
  have swap (i : ι) : within s (if new i then C i else s.zero) (if old i then C i else s.zero)
      (if old i != new i then cap else s.zero) := by
    have bound := between_zero s (bounded i)
    cases old i <;> cases new i <;>
      first | exact within_self s _ _ | exact bound | exact ⟨bound.2,bound.1⟩
  have keep (i : ι) : within s (if old i then C i else s.zero) (if old i then c i else s.zero)
      (if old i then shift else s.zero) := by
    cases h : old i <;> first | exact within_self s _ _ | exact drift i
  apply within_chain s
  · apply grow s (balance_sum s L _ _ _ swap)
    exact on_bits s L _ _ cap (fun _ _ _ => s.refl _)
  · apply grow s (balance_sum s L _ _ _ keep)
    exact on_bits s L old _ shift (fun _ _ _ => s.refl _)

/-- Reorder the actual signedPart sum by masks. -/
theorem by_mask {n} (x : State n) (z : Cell n) (p : Cell n → Fin 4 → α)
    (v : α) (b : Cell n → α) (j : Bool) :
    s.sum (board n) (fun e => signedPart s x z e (p e) v (b e) j) =
    s.sum (masks j) (fun l =>
      gated s (board n) (occBit x z l) (fun e => coeff s (p e) v (keys l)) ⊞
      gated s (board n) (avBit x z l) (fun e => b e ⊗ coeff s (p e) v (keys l))) := by
  classical
  simp only [as_dual,dualPart,exchange_sum s (board n),add_sum,gated]
  have eq (o : Bool) (e : Cell n) (l : Marks) (v : α) : v ⊗ bit s o x z e l =
      if pattern o x z e l then v else s.zero := by
    by_cases h : pattern o x z e l <;> simp [h,bit,s.mulOne,s.mulZero]
  simp only [eq,pattern,if_true,Bool.false_eq_true,if_false,occBit,avBit,decide_eq_true_eq]

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.support_jump
#print axioms ArticuloA.Trayectoria.Adjunto.by_mask
