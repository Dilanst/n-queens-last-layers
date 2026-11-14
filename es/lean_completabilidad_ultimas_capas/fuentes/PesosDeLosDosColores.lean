import ProcesoE2
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

/-- At positive hole levels the two colors use the same vertex factors. -/
def sameColors (u : Fin 4 → Nat → α) : ColorWeights α := ⟨u,u⟩

/-- At level zero real edges use the full profile. Virtual edges have zero
physical row/column factors and unit dummy row/column factors. -/
def fullColors (n : Nat) (r c d a : Nat → α) : ColorWeights α where
  real := fun | 0 => r | 1 => c | 2 => d | 3 => a
  virtual := fun | 0 => fun i => if i < n then s.zero else s.one
                 | 1 => fun j => if j < n then s.zero else s.one
                 | 2 => d | 3 => a

theorem sharedChoices {n} (x : State n) (u : Fin 4 → Nat → α) :
    realChoices s x (sameColors u) =
    ((board n).filter (fun e => available x (lines e))).map (fun e =>
      (weights s u (lines e), Choice.real e)) := rfl

theorem full_real {n} (r c d a : Nat → α) (e : Cell n) :
    weights s (fullColors s n r c d a).real (lines e) =
      s.mul (s.mul (r e.1.val) (c e.2.val)) (s.mul (d (lines e 2)) (a (lines e 3))) := rfl

theorem full_virtual {n} (r c d a : Nat → α) (g : Edge) :
    weights s (fullColors s n r c d a).virtual g =
    if g 0 < n ∨ g 1 < n then s.zero else s.mul (d (g 2)) (a (g 3)) := by
  have z (v : α) : s.mul s.zero v = s.zero := by rw [s.mulComm,s.mulZero]
  by_cases hr : g 0 < n <;> by_cases hc : g 1 < n <;>
    simp [weights,ProfileScale.four,fullColors,hr,hc,z,s.mulZero,s.oneMul]
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.sharedChoices
#print axioms ArticuloA.Trayectoria.E2.full_real
#print axioms ArticuloA.Trayectoria.E2.full_virtual
