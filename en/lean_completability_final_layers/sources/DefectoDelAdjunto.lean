import CuatroLineas
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2.Regular Control
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩

theorem single_balance (p : ι → α) (v a tail : α) (sum : v ⊞ tail = s.one) (J : List ι) :
    ((a ⊗ tail) ⊗ slope s p v J) ⊞ ((ns s J.length ⊗ a) ⊗ coeff s p v J) =
      a ⊗ predecessor s (coeff s p v) p J := by
  rw [←slope_deletions]
  have h := homogeneous s p v J
  rw [times_m] at h
  calc
    _ = a ⊗ ((tail ⊗ slope s p v J) ⊞ (ns s J.length ⊗ coeff s p v J)) := by rw [s.mulAdd]; ac_rfl
    _ = _ := by rw [←h,←s.addMul,s.comm tail v,sum,s.oneMul]

/-- Finite-difference adjoint for an occupied coefficient in its parity sign.
No derivative or time discretization is assumed. -/
theorem occupied_residue (p : ι → α) (v a tail : α) (sum : v ⊞ tail = s.one) (J : List ι) :
    let g := a ⊗ tail
    let C := coeff s p v J
    let rem := (g ⊗ g) ⊗ second s p v (v ⊞ g) J
    (coeff s p (v ⊞ g) J) ⊞ ((ns s J.length ⊗ a) ⊗ C) =
      (C ⊞ (a ⊗ predecessor s (coeff s p v) p J)) ⊞ rem := by
  dsimp only
  rw [expansion,←single_balance s p v a tail sum]; ac_rfl

theorem feed_balance {r a old new k : α} (split : old = k ⊞ (quart s r ⊗ new))
    (sum : r ⊞ a = s.one) :
    old ⊞ ((s.times 4 a) ⊗ new) = (k ⊞ new) ⊞ (((a ⊗ a) ⊗ lag s r 4) ⊗ new) := by
  rw [split,s.assoc,←s.addMul,four_correction s r a sum,s.addMul,s.oneMul,s.assoc]

theorem feed_change {r a old new k : α} (split : old = k ⊞ (quart s r ⊗ new))
    (sum : r ⊞ a = s.one) : within s old new (k ⊞ ((s.times 4 a) ⊗ new)) := by
  have rc : r ≼ s.one := sum ▸ up_left s r a
  have q := (size_geom s r rc 4).1
  have qp : power s r 4 = quart s r := by simp only [power,s.mulOne,quart,s.mulAssoc]
  rw [qp] at q
  have small := s.mulMono q (s.refl new)
  rw [s.oneMul] at small
  constructor
  · rw [split]
    have h := s.mono (s.refl k) small
    exact s.trans h (by rw [s.comm k new,←s.assoc]; apply up_left)
  · have h := up_left s new k
    rw [s.comm new k] at h
    have bigger := s.trans h (up_left s (k ⊞ new) (((a ⊗ a) ⊗ lag s r 4) ⊗ new))
    rw [←feed_balance s split sum] at bigger
    apply s.trans bigger (s.mono (s.refl old) _)
    rw [s.comm k]; apply up_left

/-- The exact mixed term is controlled by the change of the feed coefficient
times the linear increment. The remaining two errors are quadratic. -/
theorem available_residue (p : ι → α) (v a tail r old new k : α) (sum : v ⊞ tail = s.one)
    (alive : r ⊞ a = s.one) (split : old = k ⊞ (quart s r ⊗ new)) (J : List ι) :
    let g := a ⊗ tail
    let C := coeff s p v J
    let inc := g ⊗ slope s p v J
    let rem := (g ⊗ g) ⊗ second s p v (v ⊞ g) J
    let step := (ns s J.length ⊗ a)
    let err := ((k ⊞ ((s.times 4 a) ⊗ new)) ⊗ inc) ⊞
      ((old ⊗ rem) ⊞ ((((a ⊗ a) ⊗ lag s r 4) ⊗ new) ⊗ C))
    within s ((old ⊗ coeff s p (v ⊞ g) J) ⊞ (((s.times 4 a ⊞ step) ⊗ new) ⊗ C))
      (((new ⊗ C) ⊞ (new ⊗ (a ⊗ predecessor s (coeff s p v) p J))) ⊞ (k ⊗ C)) err := by
  intro g C inc rem step err
  let extra := ((old ⊗ rem) ⊞ ((((a ⊗ a) ⊗ lag s r 4) ⊗ new) ⊗ C))
  let core := ((k ⊞ new) ⊗ C) ⊞ ((step ⊗ new) ⊗ C)
  have h := scale s inc (feed_change s split alive)
  rw [s.mulComm inc old,s.mulComm inc new,s.mulComm inc (_ ⊞ _)] at h
  have add := within_add s (within_self s core s.zero) (within_add s h
    (show within s extra s.zero extra from ⟨by rw [s.zero_add]; exact s.refl _,s.zero_le _⟩))
  rw [s.zero_add,s.comm (new ⊗ inc) s.zero,s.zero_add] at add
  change within s _ _ err
  have eqL : ((old ⊗ coeff s p (v ⊞ g) J) ⊞ (((s.times 4 a ⊞ step) ⊗ new) ⊗ C)) =
      core ⊞ ((old ⊗ inc) ⊞ extra) := by
    rw [expansion,s.mulAdd old,s.mulAdd old,s.addMul,s.addMul]
    dsimp only [core,extra,inc,rem,C,g,step]
    have re := congrArg (fun x => x ⊗ coeff s p v J) (feed_balance s split alive)
    simp only [s.addMul] at re
    rw [s.addMul]
    calc
      _ = ((old ⊗ coeff s p v J) ⊞ (((s.times 4 a) ⊗ new) ⊗ coeff s p v J)) ⊞
        (((old ⊗ inc) ⊞ (old ⊗ rem)) ⊞ ((step ⊗ new) ⊗ C)) := by dsimp only [g,C,inc,rem,step]; ac_rfl
      _ = _ := by rw [re]; dsimp only [inc,rem,C,step,g]; ac_rfl
  have eqR : (((new ⊗ C) ⊞ (new ⊗ (a ⊗ predecessor s (coeff s p v) p J))) ⊞ (k ⊗ C)) =
      core ⊞ (new ⊗ inc) := by rw [←single_balance s p v a tail sum,s.mulAdd]; unfold core; rw [s.addMul]; dsimp only [inc,step,C,g]; ac_rfl
  rw [eqL,eqR]; exact add

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.occupied_residue
#print axioms ArticuloA.Trayectoria.Adjunto.available_residue
