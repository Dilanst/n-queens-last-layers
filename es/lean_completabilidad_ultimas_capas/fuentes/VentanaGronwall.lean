import GronwallDiscreto
namespace ArticuloA.Trayectoria.Control
open ArticuloA.Corte E2.Regular
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le

theorem split_window (n D : Nat) (dpos : 0 < D) (big : 2*D ≤ n) :
    let m := n/(2*D)
    (2*m)*D ≤ n ∧ 2*n ≤ (8*D)*m := by
  let k := 2*D
  have kp : 0 < k := by dsimp [k]; omega
  have mp : 0 < n/k := Nat.div_pos big kp
  have lo := Nat.div_mul_le_self n k
  have rem := Nat.mod_lt n kp
  have rep := Nat.mod_add_div n k
  have extra : k ≤ k*(n/k) := by simpa using Nat.mul_le_mul_left k (show 1 ≤ n/k from mp)
  have hi : n ≤ 2*(k*(n/k)) := by omega
  have up := Nat.mul_le_mul_left 2 hi
  dsimp only
  constructor
  · simpa [k,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using lo
  · calc
      _ ≤ _ := up
      _ = _ := by dsimp [k]; change _ = ((2*2*2)*D)*(n/(2*D)); ac_rfl

theorem paper_window (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (E : Nat → α) (a L : α) (T stop n D : Nat) (big : 2*D ≤ n) (dp : 0 < D)
    (nz : ns s n ≠ s.zero) (hL : L ≼ (inv (ns s n) ⊗ ns s D)) (duration : T ≤ 2*n)
    (err : ∀ t ≤ min T stop, E t ≼ (a ⊞ (L ⊗ historySum s E t))) (t : Nat) (ht : t ≤ T) :
    E (min t stop) ≼ (power s (s.one ⊞ s.one) (8*D) ⊗ a) := by
  let m := n/(2*D)
  obtain ⟨len,span⟩ := split_window n D dp big
  apply stopped_bound s E T m (8*D) stop a L err _ (Nat.le_trans duration span) t ht
  have h : s.times m (L ⊞ L) = ns s (2*m) ⊗ L := by
    rw [times_m,size_mult,s.mulAdd]
    change _ = ((s.one ⊞ (s.one ⊞ s.zero)) ⊗ ns s m) ⊗ L
    rw [s.comm s.one s.zero,s.zero_add,s.addMul,s.oneMul,s.addMul]
  rw [h]
  have first := s.mulMono (s.refl (ns s (2*m))) hL
  have eq : ns s (2*m) ⊗ (inv (ns s n) ⊗ ns s D) = inv (ns s n) ⊗ ns s ((2*m)*D) := by
    rw [size_mult s (2*m) D,←s.mulAssoc, s.mulComm (ns s (2*m)) (inv _),s.mulAssoc]
  rw [eq] at first
  have high := s.mulMono (s.refl (inv (ns s n))) (le_times s len s.one)
  change s.le (inv (ns s n) ⊗ ns s ((2*m)*D)) (inv (ns s n) ⊗ ns s n) at high
  rw [recip _ nz] at high
  exact s.trans first high

end ArticuloA.Trayectoria.Control
#print axioms ArticuloA.Trayectoria.Control.paper_window
