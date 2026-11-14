import ColaFinita
import UnionCorte

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

/-- One vertex from each of the four distinct parts. -/
abbrev Edge := Fin 4 → Nat
def lines {n} (e : Cell n) : Edge
  | 0 => e.1.val
  | 1 => e.2.val
  | 2 => e.1.val+(n-1-e.2.val)
  | 3 => e.1.val+e.2.val

def virtualEdges (N : Nat) : List Edge := (List.range N).flatMap fun i =>
  (List.range N).flatMap fun j => (List.range N).flatMap fun d =>
    (List.range N).map fun a => fun | 0 => i | 1 => j | 2 => d | 3 => a

structure State (n : Nat) where
  reals : Nat
  virtuals : Nat
  active : Fin 4 → Nat → Bool
  physical : Placement n
  failed : Bool

def emptyMask {α : Type} : (xs : List α) → Mask xs
  | [] => .empty
  | _ :: xs => .skip (emptyMask xs)
def initial (n h : Nat) : State n :=
  ⟨n-h,(2*n-1)-(n-h),fun _ _ => true,emptyMask (board n),false⟩
def available {n} (x : State n) (e : Edge) := (List.finRange 4).all (fun i => x.active i (e i))
def consume {n} (x : State n) (edge : Edge) := fun i j => x.active i j && (j != edge i)
inductive Choice (n : Nat)
  | real (c : Cell n)
  | virtual (v : Edge)
  | fail

def next {n} (x : State n) : Choice n → State n
  | .real c => { x with reals := x.reals-1, active := consume x (lines c), physical := toggle c x.physical }
  | .virtual e => { x with virtuals := x.virtuals-1, active := consume x e }
  | .fail => { x with failed := true }

theorem virtual_physical {n} (x : State n) (e : Edge) :
    (next x (.virtual e)).physical = x.physical ∧ (next x (.virtual e)).reals = x.reals :=
  ⟨rfl,rfl⟩

variable {α : Type} (s : ProfileScale α)
structure ColorWeights (α : Type) where
  real : Fin 4 → Nat → α
  virtual : Fin 4 → Nat → α

instance : CoeFun (ColorWeights α) (fun _ => Fin 4 → Nat → α) := ⟨ColorWeights.virtual⟩

def weights (u : Fin 4 → Nat → α) (e : Edge) := s.four (fun i => u i (e i))
def realChoices {n} (x : State n) (u : ColorWeights α) : Atoms α (Choice n) :=
  ((board n).filter (fun c => available x (lines c))).map (fun c => (weights s u.real (lines c),.real c))
def virtualChoices {n} (x : State n) (u : Fin 4 → Nat → α) : Atoms α (Choice n) :=
  ((virtualEdges (2*n-1)).filter (available x)).map (fun e => (weights s u e,.virtual e))

/-- Conditional colour quotas from remaining counts. Inputs u and inv can be real;
this definition enumerates no paths unless evaluated. Failed states and final
states are absorbing, including their physical placement. -/
noncomputable def kernel {n} (u : ColorWeights α) (inv : α → α)
    (_ : Nat) (x : State n) : Atoms α (State n) := by
  classical
  let r := s.times x.reals s.one
  let v := s.times x.virtuals s.one
  let den := s.add r v
  exact if x.failed || (x.reals+x.virtuals == 0) then point s x else
    (mixture s (s.mul (inv den) r) (s.mul (inv den) v)
      (choose s (realChoices s x u) .fail inv)
      (choose s (virtualChoices s x u) .fail inv)).map (fun i => (i.1,next x i.2))

theorem kernel_total {n} (u : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (pos : ∀ i j : Nat, i+j ≠ 0 → s.add (s.times i s.one) (s.times j s.one) ≠ s.zero)
    (t : Nat) (x : State n) : total s (kernel s u inv t x) = s.one := by
  classical
  unfold kernel
  split
  · exact avg_point s _ _
  · rename_i live
    have count : x.reals+x.virtuals ≠ 0 := by intro h; simp [h] at live
    unfold total
    rw [avg_push]
    apply mixture_total s _ _ _ _ (choose_total s _ _ _ recip) (choose_total s _ _ _ recip)
    rw [← s.mulAdd]; exact recip _ (pos _ _ count)

theorem law_one {n} (u : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (pos : ∀ i j : Nat, i+j ≠ 0 → s.add (s.times i s.one) (s.times j s.one) ≠ s.zero)
    (steps : Nat) (x : State n) :
    total s (leaves s (kernel s u inv) 0 steps x) = s.one := by
  unfold total
  rw [leaf_expectation]; exact probability_one s _ (kernel_total s u inv recip pos) _ _ _

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.kernel_total
#print axioms ArticuloA.Trayectoria.E2.law_one
