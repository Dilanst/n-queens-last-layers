import DerivaEnRegion
namespace ArticuloA.Trayectoria.Control
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le

def historySum (E : Nat → α) : Nat → α
  | 0 => s.zero
  | k+1 => historySum E k ⊞ E k

def power (a : α) : Nat → α
  | 0 => s.one
  | k+1 => a ⊗ power a k

theorem pow_add (a : α) (m j : Nat) :
    power s a (m+j) = power s a m ⊗ power s a j := by
  induction m with
  | zero => simp [power,s.oneMul]
  | succ m ih => rw [Nat.succ_add]; change a ⊗ _ = (a ⊗ _) ⊗ _
                 rw [ih,s.mulAssoc]

theorem step_bound (E : Nat → α) (a L : α) (T : Nat)
    (err : ∀ t ≤ T, E t ≼ (a ⊞ (L ⊗ historySum s E t))) (t : Nat) (ht : t ≤ T) :
    E t ≼ (power s (s.one ⊞ L) t ⊗ a) := by
  let H := fun t => a ⊞ (L ⊗ historySum s E t)
  have envelope (k : Nat) (hk : k ≤ T) : H k ≼ (power s (s.one ⊞ L) k ⊗ a) := by
    induction k with
    | zero => simp [H,historySum,power,s.mulZero,s.comm a s.zero,s.zero_add,s.oneMul,s.refl]
    | succ j ih =>
      have prev := ih (Nat.le_of_succ_le hk)
      have h := s.mono prev (s.mulMono (s.refl L) (s.trans (err j (by omega)) prev))
      change s.le (a ⊞ (L ⊗ (historySum s E j ⊞ E j))) (((s.one ⊞ L) ⊗ power s (s.one ⊞ L) j) ⊗ a)
      rw [s.mulAdd,←s.assoc,s.mulAssoc,s.addMul,s.oneMul]; exact h
  exact s.trans (err t ht) (envelope t ht)

/-- On a short block the envelope cannot grow by more than a factor two.
The size condition is stated without division. -/
theorem short_power (L : α) (m : Nat)
    (small : s.times m (s.add L L) ≼ s.one) (j : Nat) (hj : j ≤ m) :
    power s (s.one ⊞ L) j ≼ (s.one ⊞ s.one) := by
  have bound (k : Nat) (hk : k ≤ m) :
      power s (s.one ⊞ L) k ≼ (s.one ⊞ s.times k (L ⊞ L)) := by
    induction k with
    | zero => simpa [power,MassScale.times,s.comm _ s.zero,s.zero_add] using s.refl s.one
    | succ i ih =>
      have old := ih (by omega)
      have two := s.trans old (s.mono (s.refl _) (s.trans (le_times s (show i ≤ m by omega) _) small))
      have gain := s.mulMono (s.refl L) two
      rw [s.mulAdd,s.mulOne] at gain
      have h := s.mono old gain
      change s.le ((s.one ⊞ L) ⊗ power s (s.one ⊞ L) i) (s.one ⊞ ((L ⊞ L) ⊞ s.times i (L ⊞ L)))
      rw [s.addMul,s.oneMul,s.comm (L ⊞ L) (s.times i _),←s.assoc]; exact h
  exact s.trans (bound j hj) (s.mono (s.refl _) (s.trans (le_times s hj _) small))

theorem blocks (L : α) (m B t : Nat) (small : s.times m (L ⊞ L) ≼ s.one) (span : t ≤ B*m) :
    power s (s.one ⊞ L) t ≼ power s (s.one ⊞ s.one) B := by
  induction B generalizing t with
  | zero => have : t = 0 := by omega
            subst t; exact s.refl _
  | succ B ih =>
    let j := min m t
    have cap : t-j ≤ B*m := by dsimp [j]; rw [Nat.succ_mul] at span; omega
    have split : t = j+(t-j) := by dsimp [j]; omega
    calc
      _ = power s (s.one ⊞ L) j ⊗ power s (s.one ⊞ L) (t-j) := congrArg (power s _) split |>.trans (pow_add s _ _ _)
      _ ≼ _ := s.mulMono (short_power s L m small j (Nat.min_le_left ..)) (ih _ cap)

theorem stopped_bound (E : Nat → α) (T m B stop : Nat) (a L : α)
    (err : ∀ t ≤ min T stop, E t ≼ (a ⊞ (L ⊗ historySum s E t)))
    (small : s.times m (L ⊞ L) ≼ s.one) (span : T ≤ B*m) (t : Nat) (ht : t ≤ T) :
    E (min t stop) ≼ (power s (s.one ⊞ s.one) B ⊗ a) := by
  have h : min t stop ≤ min T stop := by omega
  exact s.trans (step_bound s E a L _ err _ h)
    (s.mulMono (blocks s L m B _ small (by omega)) (s.refl _))
end ArticuloA.Trayectoria.Control
#print axioms ArticuloA.Trayectoria.Control.stopped_bound
