import MasasDelTablero
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def ns (n : Nat) := s.times n s.one
def timeMass {n} (x : State n) := s.add (ns s x.reals) (ns s x.virtuals)
def norm (inv : α → α) (size raw : α) := inv size ⊗ raw

theorem restore (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {size : α} (live : size ≠ s.zero) (raw : α) : size ⊗ norm s inv size raw = raw := by
  rw [norm,←s.mulAssoc,s.mulComm size,recip _ live,s.oneMul]

theorem board_coordinates {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (v : Cell n → α) (a : α)
    (weight : ∀ e, weights s w.real (lines e) = a ⊗ v e)
    (sn : ns s n ≠ s.zero) (sq : ns s n ⊗ ns s n ≠ s.zero) (time : timeMass s x ≠ s.zero)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero)
    (j : Vertex) (e : Cell n) (live : j.2 < 2*n-1 ∧ x.active j.1 j.2) :
    let size := ns s n
    let normal := norm s inv size
    let T := normal (timeMass s x)
    let W := norm s inv (size ⊗ size) (boardSum s v (fun e => available x (lines e)))
    let D := normal (auxDegree s x v j)
    let U := normal (Cart.part s x w j.1)
    let Q := normal (ns s x.reals)
    let H := normal (ns s x.virtuals)
    (T ⊗ W) ⊗ (size ⊗ realRate s x w inv j) = Q ⊗ D ∧
    (T ⊗ U) ⊗ (size ⊗ virtRate s x w inv j) = H ⊗ w j.1 j.2 ∧
    (T ⊗ W) ⊗ ((size ⊗ size) ⊗ realAtom s x w inv e) = Q ⊗ v e := by
  dsimp only
  obtain ⟨wr,dr⟩ := scaled_totals s x w v a weight j live.2
  apply kernel_coordinates s x w inv recip j e rr vv live
  · exact clock_quota s inv recip sn time (restore s inv recip sn _) (restore s inv recip sn _)
  · exact clock_quota s inv recip sn time (restore s inv recip sn _) (restore s inv recip sn _)
  · rw [s.mulComm (ns s n ⊗ ns s n) a,s.mulAssoc,restore s inv recip sq,wr]
  · rw [s.mulComm (ns s n) a,s.mulAssoc,restore s inv recip sn,dr]
  · exact (weight e).symm
  · exact restore s inv recip sn _

theorem colour_mass {n} (x : State n) (inv : α → α) :
    s.add (norm s inv (ns s n) (ns s x.reals)) (norm s inv (ns s n) (ns s x.virtuals)) =
    norm s inv (ns s n) (timeMass s x) := (s.mulAdd _ _ _).symm

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.board_coordinates
