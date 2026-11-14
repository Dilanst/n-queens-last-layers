import Std

namespace ArticuloA.Corte

/-- Algebra used for nonnegative masses. No hypothesis about the queens or E2. -/
structure MassScale (α : Type) extends LE α, Add α, Zero α where
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  zero_le : ∀ a, le zero a
  zero_add : ∀ a, add zero a = a
  comm : ∀ a b, add a b = add b a
  assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)

/-- Additional laws for the nonnegative scalars used by the deterministic profile. -/
structure ProfileScale (α : Type) extends MassScale α, Mul α where
  one : α
  cancel : ∀ {a b c}, le (add a c) (add b c) → le a b
  halfOrder : ∀ {a b}, le (add a a) (add b b) → le a b
  mulMono : ∀ {a b c d}, le a b → le c d → le (mul a c) (mul b d)
  mulAdd : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  addMul : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  mulZero : ∀ a, mul a zero = zero
  mulOne : ∀ a, mul a one = a
  oneMul : ∀ a, mul one a = a
  mulComm : ∀ a b, mul a b = mul b a
  mulAssoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

namespace MassScale
variable {α : Type} (s : MassScale α)
def sum {ι : Type} (L : List ι) (v : ι → α) : α := L.foldr (fun i b => s.add (v i) b) s.zero
def twice (j : Nat) (a : α) : α :=
  match j with
  | 0 => a
  | j+1 => s.add (twice j a) (twice j a)
theorem sum_mono {ι} (L : List ι) (f g : ι → α) (h : ∀ i ∈ L, s.le (f i) (g i)) :
    s.le (s.sum L f) (s.sum L g) := by
  induction L with
  | nil => exact s.refl _
  | cons i L ih => exact s.mono (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))
end MassScale

namespace ProfileScale
variable {α : Type} (s : ProfileScale α)
def four (v : Fin 4 → α) := s.mul (s.mul (v 0) (v 1)) (s.mul (v 2) (v 3))
def center {ι} (L : List ι) (y : α) (π : ι → α) (v : ι → Fin 4 → α) :=
  s.mul y (s.sum L (fun e => s.mul (π e) (s.four (v e))))

/-- v = 1-y*p retains at least eta when y≤1 and p+eta≤1. -/
theorem vacancy {y p eta v : α} (time : s.le y s.one) (slack : s.le (s.add p eta) s.one)
    (factor : s.add v (s.mul y p) = s.one) : s.le eta v := by
  apply s.cancel (c := s.mul y p)
  rw [factor]
  have prod := s.mulMono time (s.refl p)
  rw [s.oneMul] at prod
  exact s.trans (s.mono (s.refl eta) prod) (by rw [s.comm]; exact slack)

private theorem sum_mul {ι} (L : List ι) (f : ι → α) (b : α) :
    s.sum L (fun e => s.mul (f e) b) = s.mul (s.sum L f) b := by
  induction L with
  | nil => change s.zero = s.mul s.zero b; rw [s.mulComm,s.mulZero]
  | cons e L ih => change s.add _ (s.sum L _) = s.mul (s.add _ (s.sum L f)) b; rw [ih,s.addMul]

private theorem double_mul (i j : Nat) (a b : α) :
    s.mul (s.twice i a) (s.twice j b) = s.twice (i+j) (s.mul a b) := by
  induction i with
  | zero =>
    simp only [Nat.zero_add]
    change s.mul a (s.twice j b) = s.twice j (s.mul a b)
    induction j with
    | zero => rfl
    | succ j ih => change s.mul a (s.add _ _) = s.add _ _; rw [s.mulAdd,ih]
  | succ i ih =>
    rw [Nat.succ_add]
    change s.mul (s.add _ _) _ = s.add _ _
    rw [s.addMul,ih]

private theorem reflect_double (k : Nat) {a b : α} (h : s.le (s.twice k a) (s.twice k b)) :
    s.le a b := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (s.halfOrder h)

/-- Denominator-cleared version of Phi≥2a₀n, with only the pointwise profile inputs:
4y≥1, 2∑π≥n, all four factors ≥eta, and 16 target ≤ n eta⁴. -/
theorem center_margin {ι} (L : List ι) (y n eta target : α) (π : ι → α)
    (v : ι → Fin 4 → α) (time : s.le s.one (s.twice 2 y))
    (mass : s.le n (s.twice 1 (s.sum L π))) (free : ∀ e ∈ L, ∀ i, s.le eta (v e i))
    (scale : s.le (s.twice 4 target) (s.mul n (s.four (fun _ => eta)))) :
    s.le (s.add target target) (s.center L y π v) := by
  let pow := s.four (fun _ => eta)
  have terms := s.sum_mono L (fun e => s.mul (π e) pow) _ (fun e he =>
    s.mulMono (s.refl _) (s.mulMono (s.mulMono (free e he 0) (free e he 1))
                                    (s.mulMono (free e he 2) (free e he 3))))
  rw [s.sum_mul] at terms
  have base := s.mulMono time mass
  rw [s.oneMul,s.double_mul] at base
  have major := s.mulMono base (s.refl pow)
  change s.le (s.mul n pow) (s.mul (s.twice 3 (s.mul y (s.sum L π))) (s.twice 0 pow)) at major
  rw [s.double_mul] at major
  rw [s.mulAssoc] at major
  have low := s.mulMono (s.refl y) terms
  have grow (k : Nat) {a b : α} (le : s.le a b) : s.le (s.twice k a) (s.twice k b) := by
    induction k with
    | zero => exact le
    | succ k ih => exact s.mono ih ih
  exact s.reflect_double 3 (s.trans scale (s.trans major (grow 3 low)))

end ProfileScale
end ArticuloA.Corte
#print axioms ArticuloA.Corte.ProfileScale.center_margin
