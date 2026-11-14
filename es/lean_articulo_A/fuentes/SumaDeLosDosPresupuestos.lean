import ErrorDelGeneradorPorRaiz
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem exchange_sum {ι κ : Type} (L : List ι) (M : List κ) (f : ι → κ → α) :
    s.sum L (fun i => s.sum M (f i)) = s.sum M (fun j => s.sum L (fun i => f i j)) := by
  induction L with
  | nil => change s.zero = s.sum M (fun _ => s.zero); rw [const_sum,times_m,s.mulZero]
  | cons i L ih =>
    change s.sum M (f i) ⊞ s.sum L _ = s.sum M (fun j => f i j ⊞ s.sum L (fun k => f k j))
    rw [add_sum,ih]

def sectors (w : Marks → α) := s.sum (masks false) w ⊞ s.sum (masks true) w

theorem sectors_budget {ι : Type} (L : List ι) (w : ι → Marks → α) (b : α)
    (cap : ∀ m, s.le (s.sum L (fun i => w i m)) b) :
    s.le (s.sum L (fun i => sectors s (w i))) (s.times 16 b) := by
  have per (j : Bool) := s.sum_mono (masks j) (fun m => s.sum L (fun i => w i m))
    (fun _ => b) (fun m _ => cap m)
  have h := s.mono (per false) (per true)
  simp only [const_sum,←plus_times] at h
  rw [show (masks false).length + (masks true).length = 16 by decide] at h
  simpa only [sectors,add_sum,exchange_sum s L] using h

theorem adjoint_root {n} (x : State n) (legal : Legal x.physical) (z : Cell n) (m : Marks)
    (u v : Cell n → α) (U V : α) (hu : ∀ e, s.le (u e) U) (hv : ∀ e, s.le (v e) V) :
    s.le (s.sum (board n) (fun e =>
      (bit s true x z e m ⊗ u e) ⊞ (bit s false x z e m ⊗ v e)))
      (s.times n U ⊞ s.times (n*n) V) := by
  classical
  have gate (o : Bool) (e : Cell n) (c : α) : bit s o x z e m ⊗ c =
      (if pattern o x z e m then c else s.zero) := by
    by_cases h : pattern o x z e m <;> simp [bit,h,s.oneMul,s.mulComm s.zero,s.mulZero]
  have supp := step_supports x legal z m .fail (by trivial)
  have a := s.trans (on_bits s (board n) (occBit x z m) u U (fun e _ _ => hu e)) (le_times s supp.2.2.1 U)
  have b := s.trans (on_bits s (board n) (avBit x z m) v V (fun e _ _ => hv e)) (le_times s supp.2.2.2 V)
  simpa only [add_sum,gate,pattern,if_true,Bool.false_eq_true,if_false,occBit,avBit,decide_eq_true_eq] using s.mono a b

theorem root_channels {X ι : Type} (row : Atoms α X) (L : List ι) (f : X → ι → Bool → α)
    (o : ι → Bool → α) (fw bw : ι → Marks → α) (B D : α)
    (cell : ∀ e, within s
      (avg s row (fun y => f y e false) ⊞ o e true)
      (avg s row (fun y => f y e true) ⊞ o e false) (sectors s (fw e) ⊞ sectors s (bw e)))
    (hf : ∀ m, s.le (s.sum L (fun e => fw e m)) B)
    (hb : ∀ m, s.le (s.sum L (fun e => bw e m)) D) :
    within s (avg s row (fun y => s.sum L (fun e => f y e false)) ⊞ s.sum L (fun e => o e true))
      (avg s row (fun y => s.sum L (fun e => f y e true)) ⊞ s.sum L (fun e => o e false))
      (s.times 16 B ⊞ s.times 16 D) := by
  apply grow s (root_drift s row L f o _ cell)
  rw [add_sum]; exact s.mono (sectors_budget s L fw B hf) (sectors_budget s L bw D hb)

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.root_channels
#print axioms ArticuloA.Trayectoria.Adjunto.adjoint_root
