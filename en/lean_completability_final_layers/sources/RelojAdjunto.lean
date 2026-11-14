import RestoCuadratico
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2.Regular Control
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def ratio (inv : α → α) (a b : Nat) := inv (ns s b) ⊗ ns s a

private theorem split_count (i j : Nat) : ns s (i+j) = ns s i ⊞ ns s j :=
  plus_times s i j s.one

theorem step_clock (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (m d : Nat) (fits : d ≤ m) (h : ns s m ≠ s.zero) (h' : ns s (m+1) ≠ s.zero) :
    let a := inv (ns s (m+1))
    let r := ratio s inv m (m+1)
    let v := ratio s inv d m
    let slack := ratio s inv (m-d) m
    let g := a ⊗ slack
    r ⊞ a = s.one ∧ v ⊞ slack = s.one ∧ ratio s inv (d+1) (m+1) = v ⊞ g := by
  dsimp only [ratio]
  have count : ns s d ⊞ ns s (m-d) = ns s m := by rw [←split_count,Nat.add_sub_of_le fits]
  have succ (i : Nat) : ns s i ⊞ s.one = ns s (i+1) := s.comm _ _
  have mass := congrArg (s.mul (inv (ns s m))) count
  rw [s.mulAdd,recip _ h] at mass
  have vr : (inv (ns s m) ⊗ ns s d) ⊗ (inv (ns s (m+1)) ⊗ ns s m) = inv (ns s (m+1)) ⊗ ns s d := by
    calc
      _ = (inv (ns s m) ⊗ ns s m) ⊗ (inv (ns s (m+1)) ⊗ ns s d) := by ac_rfl
      _ = _ := by rw [recip _ h,s.oneMul]
  have ra : (inv (ns s (m+1)) ⊗ ns s m) ⊞ inv (ns s (m+1)) = s.one := by
    conv => lhs; arg 2; rw [←s.mulOne (inv (ns s (m+1)))]
    rw [←s.mulAdd,succ,recip _ h']
  refine ⟨ra,mass,?_⟩
  rw [←succ d,s.mulAdd,s.mulOne,←vr]
  let v := inv (ns s m) ⊗ ns s d
  let a := inv (ns s (m+1))
  let r := a ⊗ ns s m
  let tail := inv (ns s m) ⊗ ns s (m-d)
  change (v ⊗ r) ⊞ a = v ⊞ (a ⊗ tail)
  calc
    _ = (v ⊗ r) ⊞ (a ⊗ (v ⊞ tail)) := by rw [mass,s.mulOne]
    _ = (v ⊗ (r ⊞ a)) ⊞ (a ⊗ tail) := by rw [s.mulAdd,s.mulAdd,s.mulComm a v,s.assoc]
    _ = _ := by rw [ra,s.mulOne]

def quart (a : α) := (a ⊗ a) ⊗ (a ⊗ a)
/-- k_t = pi_e * N³ / (N-t)^4, with const = pi_e*N³. -/
def rate (inv : α → α) (w : α) (m : Nat) := w ⊗ quart s (inv (ns s m))
def feed (inv : α → α) (w : α) (d m : Nat) := ns s d ⊗ rate s inv w m

theorem feed_split (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (w : α) (d m : Nat) (live : ns s m ≠ s.zero) :
    feed s inv w (d+1) (m+1) = rate s inv w (m+1) ⊞
      (quart s (ratio s inv m (m+1)) ⊗ feed s inv w d m) := by
  have q (v u : α) : quart s (v ⊗ u) = quart s v ⊗ quart s u := by unfold quart; ac_rfl
  have cancelQ : quart s (ns s m) ⊗ quart s (inv (ns s m)) = s.one := by
    rw [←q,s.mulComm _ (inv _),recip _ live]; simp only [quart,s.oneMul]
  unfold feed; change ((s.one ⊞ ns s d) ⊗ _) = _
  rw [s.addMul,s.oneMul]; apply congrArg (s.add _)
  unfold rate ratio; rw [q]
  calc
    _ = ((ns s d ⊗ (w ⊗ quart s (inv (ns s (m+1))))) ⊗
      (quart s (ns s m) ⊗ quart s (inv (ns s m)))) := by rw [cancelQ,s.mulOne]
    _ = _ := by ac_rfl

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.step_clock
#print axioms ArticuloA.Trayectoria.Adjunto.feed_split
