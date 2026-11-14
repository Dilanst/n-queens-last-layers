import MargenPerfil

namespace ArticuloA.Trayectoria
open ArticuloA.Corte

/-- A list of atoms. Separate atoms can project onto the same state. -/
abbrev Atoms (α X : Type) := List (α × X)

namespace ProfileKernel
variable {α X Y : Type} (s : ProfileScale α)
def avg (xs : Atoms α X) (f : X → α) := s.sum xs (fun a => s.mul a.1 (f a.2))
def total (xs : Atoms α X) := avg s xs (fun _ => s.one)

theorem avg_mono (xs : Atoms α X) (f g : X → α) (h : ∀ a ∈ xs, s.le (f a.2) (g a.2)) :
    s.le (avg s xs f) (avg s xs g) :=
  s.sum_mono xs _ _ (fun a ha => s.mulMono (s.refl _) (h a ha))

theorem avg_append (xs ys : Atoms α X) (f : X → α) :
    avg s (xs++ys) f = s.add (avg s xs f) (avg s ys f) := by
  induction xs with
  | nil => exact (s.zero_add _).symm
  | cons v xs ih => change s.add _ (avg s (xs++ys) f) = s.add (s.add _ (avg s xs f)) _
                    rw [ih,s.assoc]

theorem avg_scale (a : α) (xs : Atoms α X) (f : X → α) :
    avg s (xs.map (fun i => (s.mul a i.1,i.2))) f = s.mul a (avg s xs f) := by
  induction xs with
  | nil => exact (s.mulZero _).symm
  | cons v xs ih =>
    change s.add (s.mul (s.mul a v.1) _) (avg s (xs.map _) f) = s.mul a (s.add _ (avg s xs f))
    rw [ih,s.mulAssoc,s.mulAdd]

def point (x : X) : Atoms α X := [(s.one,x)]
theorem avg_point (x : X) (f : X → α) : avg s (point s x) f = f x := by
  change s.add (s.mul s.one _) s.zero = _
  rw [s.oneMul,s.comm,s.zero_add]

def mixture (r v : α) (real virtual : Atoms α X) : Atoms α X :=
  real.map (fun i => (s.mul r i.1,i.2)) ++ virtual.map (fun i => (s.mul v i.1,i.2))

theorem mixture_total (r v : α) (real virtual : Atoms α X)
    (hr : total s real = s.one) (hv : total s virtual = s.one) (hvsum : s.add r v = s.one) :
    total s (mixture s r v real virtual) = s.one := by
  unfold total at *
  rw [mixture,avg_append,avg_scale,avg_scale,hr,hv,s.mulOne,s.mulOne,hvsum]

open Classical in
/-- Positive normalizer: inv is its reciprocal. Zero normalizer: absorb in fail.
The scalar inverse law is required only at nonzero totals. -/
noncomputable def choose (edges : Atoms α X) (fail : X) (inv : α → α) : Atoms α X :=
  if total s edges = s.zero then point s fail
  else edges.map (fun i => (s.mul (inv (total s edges)) i.1,i.2))

theorem choose_total (edges : Atoms α X) (fail : X) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one) :
    total s (choose s edges fail inv) = s.one := by
  classical
  by_cases h : total s edges = s.zero
  · rw [choose,if_pos h]; exact avg_point s fail (fun _ => s.one)
  · rw [choose,if_neg h]
    exact (avg_scale s _ _ _).trans (recip _ h)

/-- The exposed colour is part of the outcome even when two edges have the
same four vertices. A missing colour class sends its entire quota to failure. -/
inductive Draw (E : Type)
  | real (e : E)
  | virtual (e : E)
  | failure (realRequested : Bool)

noncomputable def reveal (r v : α) (real virtual : Atoms α X) (inv : α → α) :
    Atoms α (Draw X) :=
  mixture s r v (choose s (real.map (fun i => (i.1,Draw.real i.2))) (.failure true) inv)
    (choose s (virtual.map (fun i => (i.1,Draw.virtual i.2))) (.failure false) inv)

theorem reveal_total (r v : α) (real virtual : Atoms α X) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one) (hs : s.add r v = s.one) :
    total s (reveal s r v real virtual inv) = s.one :=
  mixture_total s _ _ _ _ (choose_total s _ _ _ recip) (choose_total s _ _ _ recip) hs

def expectation (step : Nat → X → Atoms α X) (f : X → α) (t : Nat) : Nat → X → α
  | 0, x => f x
  | m+1, x => avg s (step t x) (expectation step f (t+1) m)

theorem probability_one (step : Nat → X → Atoms α X)
    (ok : ∀ t x, total s (step t x) = s.one) (m t : Nat) (x : X) :
    expectation s step (fun _ => s.one) t m x = s.one := by
  induction m generalizing t x with
  | zero => rfl
  | succ m ih =>
    change avg s (step t x) _ = s.one
    have eq : expectation s step (fun _ => s.one) (t+1) m = fun _ => s.one :=
      funext (ih (t := t+1))
    rw [eq]; exact ok _ _
end ProfileKernel
end ArticuloA.Trayectoria
#print axioms ArticuloA.Trayectoria.ProfileKernel.reveal_total
#print axioms ArticuloA.Trayectoria.ProfileKernel.probability_one
