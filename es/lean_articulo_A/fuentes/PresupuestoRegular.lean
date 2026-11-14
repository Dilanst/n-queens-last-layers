import EnlaceTasas
namespace ArticuloA.Trayectoria.E2
open ArticuloA.Corte ProfileKernel
variable {n α} (s : ProfileScale α) (x : State n) (u : ColorWeights α) (inv : α → α)

/-- Uniform atom caps built from available edge weights and their true normalizers. -/
def fromWeights (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (mr mv : α) (r : ∀ e : ArticuloA.Cell n, available x (lines e) → s.le (weights s u.real (lines e)) mr)
    (v : ∀ g ∈ virtualEdges (2*n-1), available x g → s.le (weights s u g) mv) :
    AtomBounds s x u inv where
  realCap := s.mul (quota s x inv x.reals) (s.mul (inv (total s (realChoices s x u))) mr)
  virtualCap := s.mul (quota s x inv x.virtuals) (s.mul (inv (total s (virtualChoices s x u))) mv)
  realNormal := rr
  virtualNormal := vv
  capR := fun e he => s.mulMono (s.refl _) (s.mulMono (s.refl _) (r e he))
  capV := fun g hg hl => s.mulMono (s.refl _) (s.mulMono (s.refl _) (v g hg hl))

private theorem times_pull (q : Nat) (b raw : α) :
    s.times q (s.mul b raw) = s.mul b (s.times q raw) := by
  induction q with
  | zero => exact (s.mulZero _).symm
  | succ q ih =>
    change s.add (s.mul b raw) (s.times q _) = s.mul b (s.add raw _)
    rw [ih,s.mulAdd]

private theorem clear_bound (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (q : Nat) (total quota max cap : α) (nz : total ≠ s.zero)
    (h : s.le (s.times q (s.mul quota max)) (s.mul total cap)) :
    s.le (s.times q (s.mul quota (s.mul (inv total) max))) cap := by
  have eq : s.mul quota (s.mul (inv total) max) = s.mul (inv total) (s.mul quota max) := by
    rw [←s.mulAssoc,s.mulComm quota _,s.mulAssoc]
  rw [eq,times_pull]
  have v := s.mulMono (s.refl (inv total)) h
  rwa [←s.mulAssoc (inv total) total,recip _ nz,s.oneMul] at v

theorem regular_pair_scale (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (mr mv Cr Cv : α) (r : ∀ e : ArticuloA.Cell n, available x (lines e) → s.le (weights s u.real (lines e)) mr)
    (v : ∀ g ∈ virtualEdges (2*n-1), available x g → s.le (weights s u g) mv)
    (R : s.le (s.times (n*n) (s.mul (quota s x inv x.reals) mr)) (s.mul (total s (realChoices s x u)) Cr))
    (V : s.le (s.times ((n*n)*(n*n)) (s.mul (quota s x inv x.virtuals) mv)) (s.mul (s.four (Cart.part s x u)) Cv)) :
    let B := fromWeights s x u inv rr vv mr mv r v
    s.le (s.times (n*n) B.pairCap) (s.add Cr (s.times 4 Cv)) := by
  intro B
  apply B.scaledPair Cr Cv
  · exact clear_bound s inv recip _ _ _ _ _ rr R
  · rw [←Cart.normalizer] at V; exact clear_bound s inv recip _ _ _ _ _ vv V

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.regular_pair_scale
