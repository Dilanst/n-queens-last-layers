import DerivaDelCompensador
import ErrorPorRaiz
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte ArticuloA.Repair E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem board_card (n : Nat) : (board n).length = n*n := by
  unfold board
  have rows (xs : List (Fin n)) :
      (xs.flatMap (fun r => (List.finRange n).map (fun c => (r,c)))).length = xs.length*n := by
    induction xs with
    | nil => simp
    | cons r xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  rw [rows,List.length_finRange]

def fwCap (n : Nat) (b d P D : α) :=
  s.times n (s.times 4 b ⊞ s.times 6 P) ⊞ s.times (n*n) (d ⊞ (D ⊗ (s.times 8 b ⊞ s.times 28 P)))

theorem forward_root {n} (x : State n) (legal : Legal x.physical) (z : Cell n) (m : Marks)
    (b d P D : α) (atom c v : Cell n → α) (hp : ∀ e, s.le (atom e) P)
    (hc : ∀ e, s.le (c e) s.one) (hv : ∀ e, s.le (v e) D) :
    s.le (s.sum (board n) (fun e => (c e ⊗ occError s x z e m b d (atom e)) ⊞
      (v e ⊗ avError s x z e m b (atom e)))) (fwCap s n b d P D) := by
  classical
  let occ := s.times 4 b ⊞ s.times 6 P
  let av := s.times 8 b ⊞ s.times 28 P
  have tm (i : Nat) (e : Cell n) : s.le (s.times i (atom e)) (s.times i P) := by
    rw [times_m,times_m]; exact s.mulMono (s.refl _) (hp e)
  have dGate (e : Cell n) : s.le (if availPattern x z e m then d else s.zero) d := by
    split <;> first | exact s.refl _ | exact s.zero_le _
  have eo (e : Cell n) : s.le (occError s x z e m b d (atom e))
      ((if occBit x z m e then occ else s.zero) ⊞ d) := by
    by_cases h : occupied x z e m
    · simpa only [occError,occBit,h,if_true,indicator,decide_true,Nat.one_mul,occ,s.assoc,s.comm d (s.times 6 P)] using
        s.mono (s.refl (s.times 4 b)) (s.mono (dGate e) (tm 6 e))
    · simpa [occError,occBit,h,indicator,MassScale.times,s.zero_add,s.comm _ s.zero] using dGate e
  have ev (e : Cell n) : s.le (avError s x z e m b (atom e)) av := by
    unfold avError av
    apply s.mono (s.refl _)
    by_cases h : availPattern x z e m
    · simpa only [indicator,h,if_true,Nat.one_mul] using tm 28 e
    · simp only [indicator,h,if_false,Nat.zero_mul,MassScale.times]; exact s.zero_le _
  have localCap (e : Cell n) : s.le
      ((c e ⊗ occError s x z e m b d (atom e)) ⊞ (v e ⊗ avError s x z e m b (atom e)))
      ((if occBit x z m e then occ else s.zero) ⊞ (d ⊞ (D ⊗ av))) := by
    simpa only [s.oneMul,s.assoc] using s.mono (s.mulMono (hc e) (eo e)) (s.mulMono (hv e) (ev e))
  have allE := s.sum_mono (board n) _ _ (fun e _ => localCap e)
  rw [add_sum s (board n) (fun e => if occBit x z m e then occ else s.zero) (fun _ => d ⊞ (D ⊗ av)),
    const_sum,board_card] at allE
  have bound := on_bits s (board n) (occBit x z m) (fun _ => occ) occ (fun _ _ _ => s.refl _)
  exact s.trans allE (s.mono (s.trans bound (le_times s (occ_support x legal z m) _)) (s.refl _))

/-- Explicit size dependence: with B=n*b, V=n²*d, L=n*D and J=n²*P,
the only pair terms carry J/n. This identity uses n*P directly. -/
theorem fw_units (n : Nat) (b d P D : α) :
    fwCap s n b d P D =
      (s.times 4 (ns s n ⊗ b) ⊞ s.times 6 (ns s n ⊗ P)) ⊞
      (((ns s n ⊗ ns s n) ⊗ d) ⊞ ((ns s n ⊗ D) ⊗ (s.times 8 (ns s n ⊗ b) ⊞ s.times 28 (ns s n ⊗ P)))) := by
  simp only [fwCap,times_m,size_mult,s.mulAdd]
  ac_rfl

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.forward_root
#print axioms ArticuloA.Trayectoria.Adjunto.fw_units
