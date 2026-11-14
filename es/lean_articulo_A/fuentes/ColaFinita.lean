import LeyRamas

namespace ArticuloA.Trayectoria.ProfileKernel
open ArticuloA.Corte
variable {α X Y : Type} (s : ProfileScale α)

theorem avg_push (xs : Atoms α X) (g : X → Y) (f : Y → α) :
    avg s (xs.map (fun i => (i.1,g i.2))) f = avg s xs (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    change s.add (s.mul v.1 (f (g v.2))) (avg s (xs.map (fun i => (i.1,g i.2))) f) =
      s.add _ (avg s xs (fun x => f (g x)))
    rw [ih]

theorem avg_mul (xs : Atoms α X) (a : α) (f : X → α) :
    avg s xs (fun x => s.mul a (f x)) = s.mul a (avg s xs f) := by
  induction xs with
  | nil => exact (s.mulZero _).symm
  | cons v xs ih =>
    change s.add (s.mul v.1 (s.mul a (f v.2))) (avg s xs (fun x => s.mul a (f x))) =
      s.mul a (s.add (s.mul v.1 (f v.2)) (avg s xs f))
    rw [ih,s.mulAdd,← s.mulAssoc,s.mulComm v.1 a,s.mulAssoc]

def bindAtoms (xs : Atoms α X) (g : X → Atoms α Y) : Atoms α Y :=
  xs.flatMap (fun v => (g v.2).map (fun i => (s.mul v.1 i.1,i.2)))

theorem avg_bind (xs : Atoms α X) (g : X → Atoms α Y) (f : Y → α) :
    avg s (bindAtoms s xs g) f = avg s xs (fun x => avg s (g x) f) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    change avg s (((g v.2).map (fun i => (s.mul v.1 i.1,i.2))) ++ bindAtoms s xs g) f =
      s.add (s.mul v.1 (avg s (g v.2) f)) (avg s xs (fun x => avg s (g x) f))
    rw [avg_append,avg_scale,ih]

def leaves (step : Nat → X → Atoms α X) (t : Nat) : Nat → X → Atoms α X
  | 0, x => point s x
  | m+1, x => bindAtoms s (step t x) (leaves step (t+1) m)

theorem leaf_expectation (step : Nat → X → Atoms α X) (f : X → α) (t m : Nat) (x : X) :
    avg s (leaves s step t m x) f = expectation s step f t m x := by
  induction m generalizing t x with
  | zero => exact avg_point s x f
  | succ m ih =>
    change avg s (bindAtoms s _ _) f = avg s (step t x) _
    rw [avg_bind,show (fun y => avg s (leaves s step (t+1) m y) f) =
      expectation s step f (t+1) m from funext (ih (t := t+1))]

/-- The stored time freezes together with the state. A jump *into* the stopped
set uses the original transition, including a possible failure outcome. -/
def stopped (step : Nat → X → Atoms α X) (halt : Nat → X → Bool) (_ : Nat)
    (v : Nat × X) : Atoms α (Nat × X) :=
  if halt v.1 v.2 then point s v else
    (step v.1 v.2).map (fun i => (i.1,(v.1+1,i.2)))

theorem stopped_total (step : Nat → X → Atoms α X) (halt : Nat → X → Bool)
    (norm : ∀ t x, total s (step t x) = s.one) (u : Nat) (v : Nat × X) :
    total s (stopped s step halt u v) = s.one := by
  unfold stopped total
  split
  · exact avg_point s _ _
  · rw [avg_push]; exact norm _ _

def power (a : α) : Nat → α
  | 0 => s.one
  | m+1 => s.mul (power a m) a

/-- Local positive transform bound implies a terminal bound after m steps.
The transition weights are those of the original tree, including failed branches. -/
theorem transform_bound (step : Nat → X → Atoms α X) (H : Nat → X → α)
    (a : α) (localBound : ∀ u x, s.le (avg s (step u x) (H (u+1))) (s.mul a (H u x)))
    (t m : Nat) (x : X) :
    s.le (expectation s step (H (t+m)) t m x) (s.mul (power s a m) (H t x)) := by
  induction m generalizing t x with
  | zero => rw [power,s.oneMul]; exact s.refl _
  | succ m ih =>
    have eq : t+(m+1) = (t+1)+m := by omega
    rw [eq]
    change s.le (avg s (step t x) _) _
    have reduced := avg_mono s (step t x) (expectation s step (H ((t+1)+m)) (t+1) m)
      (fun y => s.mul (power s a m) (H (t+1) y)) (fun i _ => ih (t := t+1) (x := i.2))
    rw [avg_mul] at reduced
    exact s.trans reduced (by
      rw [power,s.mulAssoc]
      exact s.mulMono (s.refl _) (localBound t x))

open Classical in
noncomputable def mark (E : X → Prop) (x : X) := if E x then s.one else s.zero

/-- A finite Chernoff reduction. On a bad leaf it suffices to have
1 ≤ b·H. A geometric tail needs a quantitative local transform and threshold. -/
theorem leaf_tail (step : Nat → X → Atoms α X) (H : Nat → X → α) (E : X → Prop)
    (a b : α) (localBound : ∀ u x, s.le (avg s (step u x) (H (u+1))) (s.mul a (H u x)))
    (t m : Nat) (x : X) (bad : ∀ i ∈ leaves s step t m x, E i.2 → s.le s.one (s.mul b (H (t+m) i.2))) :
    s.le (avg s (leaves s step t m x) (mark s E))
      (s.mul b (s.mul (power s a m) (H t x))) := by
  classical
  have cmp := avg_mono s (leaves s step t m x) (mark s E) (fun y => s.mul b (H (t+m) y)) (by
    intro i hi; unfold mark; split
    · exact bad _ hi (by assumption)
    · exact s.zero_le _)
  rw [avg_mul,leaf_expectation s step (H (t+m))] at cmp
  exact s.trans cmp (s.mulMono (s.refl _) (transform_bound s step H a localBound t m x))

end ArticuloA.Trayectoria.ProfileKernel
#print axioms ArticuloA.Trayectoria.ProfileKernel.leaf_tail
#print axioms ArticuloA.Trayectoria.ProfileKernel.stopped_total
