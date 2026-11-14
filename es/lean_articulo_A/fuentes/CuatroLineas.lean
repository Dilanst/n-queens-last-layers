import RelojAdjunto
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2.Regular Control
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le

def geom (r : α) : Nat → α
  | 0 => s.zero
  | i+1 => geom r i ⊞ power s r i
def lag (r : α) : Nat → α
  | 0 => s.zero
  | i+1 => lag r i ⊞ geom s r i

theorem survive (r a : α) (sum : r ⊞ a = s.one) (j : Nat) :
    (power s r j) ⊞ (a ⊗ geom s r j) = s.one := by
  induction j with
  | zero => simp [power,geom,s.mulZero,s.comm s.one s.zero,s.zero_add]
  | succ i ih =>
    change (r ⊗ power s r i) ⊞ (a ⊗ (geom s r i ⊞ power s r i)) = s.one
    rw [s.mulAdd,s.comm (a ⊗ geom s r i),←s.assoc,←s.addMul,sum,s.oneMul,ih]

theorem missing (r a : α) (sum : r ⊞ a = s.one) (j : Nat) :
    (geom s r j) ⊞ (a ⊗ lag s r j) = ns s j := by
  induction j with
  | zero => simp [geom,lag,ns,MassScale.times,s.mulZero,s.zero_add]
  | succ i ih =>
    change (geom s r i ⊞ power s r i) ⊞ (a ⊗ (lag s r i ⊞ geom s r i)) = s.one ⊞ ns s i
    rw [s.mulAdd,←ih,←survive s r a sum i]
    have assoc : Std.Associative s.add := ⟨s.assoc⟩
    have comm : Std.Commutative s.add := ⟨s.comm⟩
    ac_rfl

theorem size_geom (r : α) (low : r ≼ s.one) (j : Nat) :
    power s r j ≼ s.one ∧ geom s r j ≼ ns s j ∧ lag s r j ≼ ns s (pairsN j) := by
  induction j with
  | zero => exact ⟨s.refl _,s.refl _,s.refl _⟩
  | succ j ih =>
    refine ⟨by simpa [power,s.oneMul] using s.mulMono low ih.1,?_,?_⟩
    · simpa [geom,s.comm (ns s j) s.one] using s.mono ih.2.1 ih.1
    · have h := s.mono ih.2.2 ih.2.1
      rw [s.comm (ns s (pairsN j))] at h
      unfold ns at h
      rw [←plus_times] at h
      exact h

theorem four_correction (r a : α) (sum : r ⊞ a = s.one) :
    (quart s r) ⊞ (s.times 4 a) = s.one ⊞ ((a ⊗ a) ⊗ lag s r 4) := by
  have surv := survive s r a sum 4
  have qp : power s r 4 = quart s r := by simp only [power,s.mulOne,quart,s.mulAssoc]
  rw [qp] at surv
  rw [←surv,s.assoc,s.mulAssoc,←s.mulAdd,missing s r a sum,times_m,s.mulComm a]
end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.four_correction
