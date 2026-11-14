import MartingalaDeHistorias
import Mathlib.Tactic.Ring
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

noncomputable section
namespace ArticuloA.RealFinita
open ArticuloA.Corte ArticuloA.Trayectoria ArticuloA.Trayectoria.ProfileKernel
open scoped NNReal

def masas : ProfileScale ℝ≥0 where
  le := (· ≤ ·)
  add := (· + ·)
  zero := 0
  refl := le_refl
  trans := le_trans
  zero_le := zero_le
  zero_add := zero_add
  comm := add_comm
  assoc := add_assoc
  mono := add_le_add
  mul := (· * ·)
  one := 1
  cancel := fun h => le_of_add_le_add_right h
  halfOrder := by intro a b h; have hh : (a:ℝ) + a ≤ (b:ℝ) + b := h; change (a:ℝ) ≤ b; linarith
  mulMono := fun h g => mul_le_mul h g (zero_le _) (zero_le _)
  mulAdd := mul_add
  addMul := add_mul
  mulZero := mul_zero
  mulOne := mul_one
  oneMul := one_mul
  mulComm := mul_comm
  mulAssoc := mul_assoc

variable {X : Type}
def media : Atoms ℝ≥0 X → (X → ℝ) → ℝ
  | [], _ => 0
  | i::xs, f => (i.1:ℝ) * f i.2 + media xs f

theorem media_coe (xs : Atoms ℝ≥0 X) (f : X → ℝ≥0) :
    media xs (fun x => (f x : ℝ)) = (avg masas xs f).val := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [media,ih,avg]; rfl

theorem media_affine (xs : Atoms ℝ≥0 X) (f : X → ℝ) (a b : ℝ) :
    media xs (fun x => a + b*f x) = (total masas xs).val*a + b*media xs f := by
  induction xs with
  | nil => change 0 = 0*a+b*0; ring
  | cons i xs ih =>
    change _ = ((i.1:ℝ)*1 + (total masas xs).val)*a + b*(_ + _)
    rw [media, ih]; ring

theorem media_mono (xs : Atoms ℝ≥0 X) (f g : X → ℝ)
    (h : ∀ i ∈ xs, f i.2 ≤ g i.2) : media xs f ≤ media xs g := by
  induction xs with
  | nil => exact le_rfl
  | cons i xs ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (h i (by simp)) i.1.property)
      (ih (fun j hj => h j (by simp [hj])))

theorem media_sub (xs : Atoms ℝ≥0 X) (f g : X → ℝ≥0) :
    media xs (fun y => (f y:ℝ) - g y) = (avg masas xs f).val - (avg masas xs g).val := by
  induction xs with
  | nil => change 0 = 0 - 0; ring
  | cons i xs ih =>
    change _ = ((i.1:ℝ)*f i.2 + (avg masas xs f).val) - ((i.1:ℝ)*g i.2 + (avg masas xs g).val)
    rw [media,ih]; ring
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.media_affine
#print axioms ArticuloA.RealFinita.media_sub
