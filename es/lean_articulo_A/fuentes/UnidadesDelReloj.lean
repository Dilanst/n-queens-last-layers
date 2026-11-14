import DerivaDelCompensador
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

/-- Identify both rates directly from n*c=N, N*z=m+1 and piN=n*pi. -/
theorem physical_units {n} {x : State n} {w : ColorWeights α} {inv : α → α}
    (A : Region s x w inv) (recip : ∀ y, y ≠ s.zero → inv y ⊗ y = s.one)
    (N m : Nat) (e : Cell n) (pi : α) (live : ns s (m+1) ≠ s.zero)
    (span : ns s n ⊗ A.c = ns s N) (clock : ns s N ⊗ A.z = ns s (m+1))
    (mass : A.piN e = ns s n ⊗ pi) :
    (inv (ns s n) ⊗ inv A.time = inv (ns s (m+1))) ∧
    (inv (ns s n ⊗ ns s n) ⊗ A.birth e = rate s inv (pi ⊗ cube s (ns s N)) (m+1)) := by
  let y := ns s n
  let u := ns s N
  let r := ns s (m+1)
  have link : y ⊗ (A.c ⊗ A.z) = r := by rw [←s.mulAssoc,span,clock]
  refine ⟨(inverse_product s inv recip A.sizePos A.clockPos).symm.trans (congrArg inv link),?_⟩
  let den := (y ⊗ y) ⊗ (A.c ⊗ fourth s A.z)
  have yy := mul_live s inv recip A.sizePos A.sizePos
  have dl := mul_live s inv recip yy A.sourceClock
  have weighted : cube s u ⊗ den = y ⊗ quart s r := by
    calc
      _ = y ⊗ (((((u ⊗ u) ⊗ u) ⊗ (y ⊗ A.c))) ⊗ fourth s A.z) := by
        unfold den cube; ac_rfl
      _ = y ⊗ quart s (u ⊗ A.z) := by rw [span]; unfold quart fourth cube u; ac_rfl
      _ = _ := by rw [show u ⊗ A.z = r from clock]
  have qr : quart s (inv r) ⊗ quart s r = s.one := by
    calc
      _ = quart s (inv r ⊗ r) := by unfold quart; ac_rfl
      _ = _ := by rw [recip _ live]; simp only [quart,s.oneMul]
  have eq : (rate s inv (pi ⊗ cube s u) (m+1)) ⊗ den = (y ⊗ pi) := by
    calc
      _ = (pi ⊗ quart s (inv r)) ⊗ (cube s u ⊗ den) := by unfold rate; dsimp only [r]; ac_rfl
      _ = (y ⊗ pi) ⊗ (quart s (inv r) ⊗ quart s r) := by rw [weighted]; ac_rfl
      _ = _ := by rw [qr,s.mulOne]
  have expand : inv den = inv (y ⊗ y) ⊗ inv (A.c ⊗ fourth s A.z) :=
    inverse_product s inv recip yy A.sourceClock
  change inv (y ⊗ y) ⊗ (inv (A.c ⊗ fourth s A.z) ⊗ A.piN e) = _
  rw [←s.mulAssoc,←expand,mass,←eq]
  calc
    _ = (inv den ⊗ den) ⊗ rate s inv (pi ⊗ cube s u) (m+1) := by ac_rfl
    _ = _ := by rw [recip _ dl,s.oneMul]

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.physical_units
