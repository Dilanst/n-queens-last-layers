import PositividadRegional
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem normalize_track (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size now start phase e : α} (sn : size ≠ s.zero)
    (h : within s now (start ⊗ phase) (size ⊗ e)) :
    within s (norm s inv size now) (norm s inv size start ⊗ phase) e := by
  have est := scale s (inv size) h
  simpa only [norm,←s.mulAssoc,recip _ sn,s.oneMul] using est

theorem inverse_product (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {a b : α} (ha : a ≠ s.zero) (hb : b ≠ s.zero) : inv (a ⊗ b) = inv a ⊗ inv b := by
  have h := mul_live s inv recip ha hb
  calc
    _ = inv (a ⊗ b) ⊗ ((inv a ⊗ a) ⊗ (inv b ⊗ b)) := by rw [recip _ ha,recip _ hb,s.oneMul,s.mulOne]
    _ = (inv (a ⊗ b) ⊗ (a ⊗ b)) ⊗ (inv a ⊗ inv b) := by ac_rfl
    _ = _ := by rw [recip _ h,s.oneMul]

/-- The tracking is of W/n to tolerance eps*n, not of W to eps*n. -/
theorem normalize_board_track (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size now start phase e : α} (sn : size ≠ s.zero)
    (h : within s (norm s inv size now) (norm s inv size start ⊗ phase) (size ⊗ e)) :
    within s (norm s inv (size ⊗ size) now) (norm s inv (size ⊗ size) start ⊗ phase) e := by
  have result := normalize_track s inv recip sn h
  simpa only [norm,inverse_product s inv recip sn sn,←s.mulAssoc] using result

/-- Baseline identities from raw degree and cell masses at the initial board. -/
theorem static_loads (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size W₀ q D₀ v : α} (sn : size ≠ s.zero) (wn : W₀ ≠ s.zero) :
    let p := (inv W₀ ⊗ q) ⊗ D₀
    let piN := size ⊗ ((inv W₀ ⊗ q) ⊗ v)
    let w := norm s inv (size ⊗ size) W₀
    let initial := norm s inv size q
    w ⊗ p = initial ⊗ norm s inv size D₀ ∧ w ⊗ piN = initial ⊗ v := by
  dsimp only [norm]; rw [inverse_product s inv recip sn sn]
  constructor
  · calc
      _ = (inv W₀ ⊗ W₀) ⊗ ((inv size ⊗ q) ⊗ (inv size ⊗ D₀)) := by ac_rfl
      _ = _ := by rw [recip _ wn,s.oneMul]
  · calc
      _ = (inv W₀ ⊗ W₀) ⊗ ((inv size ⊗ size) ⊗ ((inv size ⊗ q) ⊗ v)) := by ac_rfl
      _ = _ := by rw [recip _ wn,recip _ sn,s.oneMul,s.oneMul]

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.normalize_board_track
#print axioms ArticuloA.Trayectoria.E2.Regular.static_loads
