import PerdidasEnLaBase
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2 E2.Regular
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

abbrev Co (α : Type) := List (Fin 4) → α
def dualPart (j : Bool) (C D : Co α) (O A : Marks → α) :=
  s.sum (masks j) (fun m => (C (keys m) ⊗ O m) ⊞ (D (keys m) ⊗ A m))

theorem adjust {a b c d e : α} (h : within s a b e) (l : a = c) (r : b = d) :
    within s c d e := l ▸ r ▸ h

theorem flux_scaled (j : Bool) (a : α) (p : Fin 4 → α) (C : Co α) (Z : Marks → α) :
    s.sum (masks j) (fun m => C (keys m) ⊗ (a ⊗ cross s p Z m)) =
    s.sum (masks (!j)) (fun m => (a ⊗ predecessor s C p (keys m)) ⊗ Z m) := by
  calc
    _ = a ⊗ s.sum (masks j) (fun m => C (keys m) ⊗ cross s p Z m) := by
      rw [←left_sum]; apply congrArg (s.sum _); funext m; ac_rfl
    _ = _ := by rw [flux,←left_sum]; apply congrArg (s.sum _); funext m; ac_rfl

/-- Couple the two forward types with their adjoints. The birth appears in
the occupied forward equation and the available backward equation. -/
theorem paired_step (p : Fin 4 → α) (a k : α) (C D c d : Co α)
    (O A U V fo fa bo ba : Marks → α)
    (fO : ∀ m, within s ((U m ⊞ (selfRate s true a m ⊗ O m)) ⊞ (a ⊗ cross s p O m))
      (O m ⊞ (k ⊗ A m)) (fo m))
    (fA : ∀ m, within s ((V m ⊞ (selfRate s false a m ⊗ A m)) ⊞ (a ⊗ cross s p A m))
      (A m) (fa m))
    (bO : ∀ m, within s (c (keys m) ⊞ (selfRate s true a m ⊗ C (keys m)))
      (C (keys m) ⊞ (a ⊗ predecessor s C p (keys m))) (bo m))
    (bA : ∀ m, within s (d (keys m) ⊞ (selfRate s false a m ⊗ D (keys m)))
      ((D (keys m) ⊞ (a ⊗ predecessor s D p (keys m))) ⊞ (k ⊗ C (keys m))) (ba m)) :
    let ef := fun j => dualPart s j C D fo fa
    let eb := fun j => s.sum (masks j) (fun m => (O m ⊗ bo m) ⊞ (A m ⊗ ba m))
    within s (dualPart s false C D U V ⊞ dualPart s true c d O A)
      (dualPart s true C D U V ⊞ dualPart s false c d O A)
      ((ef false ⊞ ef true) ⊞ (eb false ⊞ eb true)) := by
  intro ef eb
  let S := fun m => (C (keys m) ⊗ (selfRate s true a m ⊗ O m)) ⊞
    (D (keys m) ⊗ (selfRate s false a m ⊗ A m))
  let H := fun m => C (keys m) ⊗ (k ⊗ A m)
  let X := fun m => (C (keys m) ⊗ (a ⊗ cross s p O m)) ⊞ (D (keys m) ⊗ (a ⊗ cross s p A m))
  let Y := fun m => ((a ⊗ predecessor s C p (keys m)) ⊗ O m) ⊞ ((a ⊗ predecessor s D p (keys m)) ⊗ A m)
  let total := fun j (w : Marks → α) => s.sum (masks j) w
  have move (j : Bool) : total (!j) X = total j Y := by
    simp only [total,X,Y,add_sum,flux_scaled,Bool.not_not]
  apply signed_balance s (fun j => dualPart s j C D U V) (fun j => dualPart s j c d O A)
    (fun j => total j S) (fun j => total j X)
    (fun j => dualPart s j C D O A) (fun j => total j H) ef eb
  · intro j
    dsimp only [ef,total,dualPart]
    simp only [←add_sum]
    apply balance_sum; intro m
    have est := within_add s (scale s (C (keys m)) (fO m)) (scale s (D (keys m)) (fA m))
    simp only [s.mulAdd] at est
    apply adjust s est <;> dsimp only [S,H,X] <;> ac_rfl
  · intro j
    rw [move]; dsimp only [eb,total,dualPart]
    simp only [←add_sum]
    apply balance_sum; intro m
    have est := within_add s (scale s (O m) (bO m)) (scale s (A m) (bA m))
    simp only [s.mulAdd] at est
    apply adjust s est <;> dsimp only [S,Y,H] <;> ac_rfl

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.paired_step
