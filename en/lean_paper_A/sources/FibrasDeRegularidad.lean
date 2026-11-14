import SaltoDeUnSoporte
import TendenciaDeRegion
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel Adjunto
variable {n : Nat}
def lineOf (a : Choice n) (f : Fin 4) : Nat := match a with
  | .fail => 0 | .real c => lines c f | .virtual g => g f

theorem consumed_eq (a : Choice n) (f : Fin 4) (j : Nat) (h : consumeVertex a f j) :
    j = lineOf a f := by cases a <;> first | exact h.symm | exact h.elim

private theorem union_count {ι κ : Type} (L : List ι) (F : List κ) (hit : κ → ι → Bool)
    (b : Nat) (one : ∀ i ∈ F, L.countP (hit i) ≤ b) :
    L.countP (fun e => F.any (fun i => hit i e)) ≤ F.length*b := by
  induction F with
  | nil => simp
  | cons i F ih =>
    have head := one i (by simp)
    have tail := ih (fun j hj => one j (by simp [hj]))
    have sub (L : List ι) (p q : ι → Bool) :
        L.countP (fun e => p e || q e) ≤ L.countP p + L.countP q := by
      induction L with
      | nil => simp
      | cons a L ih => simp only [List.countP_cons]; cases p a <;> cases q a <;> simp_all <;> omega
    simp only [List.any_cons,List.length_cons,Nat.succ_mul]
    exact Nat.le_trans (sub L _ _) (by omega)

theorem fiber_cap (f : Fin 4) (j : Nat) :
    (board n).countP (fun e => hitsVertex (lines e) (f,j)) ≤ n := by
  by_cases h : 0 < n
  · let z : Cell n := (⟨0,h⟩,⟨0,h⟩)
    have cases4 : f=0 ∨ f=1 ∨ f=2 ∨ f=3 := by omega
    rcases cases4 with rfl|rfl|rfl|rfl
    · exact fibre_count z 0 j
    · exact fibre_count z 1 j
    · exact fibre_count z 2 j
    · exact fibre_count z 3 j
  · have zero : n = 0 := by omega
    subst n; exact Nat.le_refl 0

open Classical in
theorem broken_count (a : Choice n) (F : List (Fin 4)) (keep : Cell n → Bool) (b : Nat)
    (single : ∀ i ∈ F, (board n).countP (fun e => keep e && hitsVertex (lines e) (i,lineOf a i)) ≤ b) :
    (board n).countP (fun e => keep e && decide (breaks a e F)) ≤ F.length*b := by
  classical
  let hit := fun i (e : Cell n) => keep e && hitsVertex (lines e) (i,lineOf a i)
  apply Nat.le_trans _ (union_count (board n) F hit b single)
  apply List.countP_mono_left; intro e _ he
  obtain ⟨keepE,killed⟩ := Bool.and_eq_true_iff.mp he
  obtain ⟨i,hi,hv⟩ := of_decide_eq_true killed
  exact List.any_eq_true.mpr ⟨i,hi,Bool.and_eq_true_iff.mpr ⟨keepE,beq_iff_eq.mpr (consumed_eq a i _ hv)⟩⟩

variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem gate_loss_cap (x : State n) (a : Choice n) (v : Cell n → α) (keep : Cell n → Bool)
    (F : List (Fin 4)) (M : α) (cap : ∀ e, s.le (v e) M) (b : Nat)
    (single : ∀ i ∈ F, (board n).countP (fun e => keep e && hitsVertex (lines e) (i,lineOf a i)) ≤ b) :
    s.le (lostGate s x v keep F a) (s.times (F.length*b) M) := by
  classical
  let hit := fun e => keep e && decide (breaks a e F)
  have one (e : Cell n) : s.le
      (if keep e = true ∧ allLive x e F then v e ⊗ mark s (fun a => breaks a e F) a else s.zero)
      (if hit e then v e else s.zero) := by
    by_cases h : keep e = true ∧ allLive x e F
    · by_cases br : breaks a e F <;> simp [h,h.1,br,hit,mark,s.mulOne,s.mulZero,s.refl]
    · rw [if_neg h]; exact s.zero_le _
  apply s.trans (s.sum_mono (board n) _ _ (fun e _ => one e))
  exact s.trans (on_bits s (board n) hit v M (fun e _ _ => cap e)) (le_times s (broken_count a F keep b single) M)

theorem loss_to_jump {u old loss B : α} (balance : u ⊞ loss = old) (cap : s.le loss B) :
    within s u old B := by
  rw [←balance]
  exact ⟨s.trans (up_left s _ _) (up_left s _ _),s.mono (s.refl _) cap⟩

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.gate_loss_cap
