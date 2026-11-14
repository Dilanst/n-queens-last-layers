import UnidadesDelReloj
import SumaDeLosDosPresupuestos
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte ArticuloA.Repair E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

/-- Finite, uniform-in-the-root budget, with both forward and adjoint errors
in one bound on the original transition kernel. -/
theorem board_step {n} {x : State n} {w : ColorWeights α} {inv : α → α}
    (A : Region s x w inv) (good : coherent x) (legal : Legal x.physical)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero)
    (pos : ∀ i j : Nat, i+j ≠ 0 → ns s i ⊞ ns s j ≠ s.zero)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0)
    (t N m d : Nat) (fits : d ≤ m) (step : m+1 ≤ N)
    (live : ns s m ≠ s.zero) (nextPos : ns s (m+1) ≠ s.zero)
    (floor : α) (fl : floor ≠ s.zero) (margin : s.le floor (ns s m))
    (z : Cell n) (hp : ∀ e j, s.le (A.p (side j,key z e j)) s.one)
    (span : ns s n ⊗ A.c = ns s N) (clock : ns s N ⊗ A.z = ns s (m+1))
    (pi : Cell n → α) (mass : ∀ e, A.piN e = ns s n ⊗ pi e)
    (W : α) (major : ∀ e, s.le (pi e ⊗ cube s (ns s N)) W) :
    let size := ns s n
    let a := inv floor
    let K := W ⊗ quart s a
    let V := ns s N ⊗ K
    let pair := inv (size ⊗ size) ⊗ ((inv A.l ⊗ A.mr) ⊞ s.times 4 (inv (s.four (fun _ => A.l)) ⊗ A.mv))
    let b := inv size ⊗ A.combined
    let g := inv (size ⊗ size) ⊗ A.budget
    let f := fun y e j => signedPart s y z e (fun i => A.p (side i,key z e i))
      (ratio s inv d m) (feed s inv (pi e ⊗ cube s (ns s N)) d m) j
    let o := fun e j => signedPart s x z e (fun i => A.p (side i,key z e i))
      (ratio s inv (d+1) (m+1)) (feed s inv (pi e ⊗ cube s (ns s N)) (d+1) (m+1)) j
    let row := kernel s w inv t x
    within s (avg s row (fun y => s.sum (board n) (fun e => f y e false)) ⊞ s.sum (board n) (fun e => o e true))
      (avg s row (fun y => s.sum (board n) (fun e => f y e true)) ⊞ s.sum (board n) (fun e => o e false))
      (s.times 16 (fwCap s n b g pair V) ⊞
        s.times 16 (s.times n (occupiedCap s a) ⊞ s.times (n*n) (availCap s a V K))) := by
  classical
  intro size a K V pair b g f o row
  let weight := fun e => pi e ⊗ cube s (ns s N)
  let Kₑ := fun e => weight e ⊗ quart s a
  let p := fun (e : Cell n) i => A.p (side i,key z e i)
  let C := fun (e : Cell n) (l : Marks) => coeff s (p e) (ratio s inv d m) (keys l)
  let D := fun (e : Cell n) (l : Marks) => feed s inv (weight e) d m ⊗ C e l
  have physical := fun e => physical_units s A recip N m e (pi e) nextPos span clock (mass e)
  have localStep := fun e => cell_drift s A good recip proper pos running remain t N m d fits step
    live nextPos floor (weight e) fl margin z e (hp e) (physical e).1 (physical e).2
  let P := fun e => Classical.choose (localStep e)
  have localEst := fun e => Classical.choose_spec (localStep e)
  let F := fun e l => (C e l ⊗ occError s x z e l b g (P e l)) ⊞ (D e l ⊗ avError s x z e l b (P e l))
  let B := fun e l => (bit s true x z e l ⊗ occupiedCap s a) ⊞
    (bit s false x z e l ⊗ availCap s a (ns s N ⊗ Kₑ e) (Kₑ e))
  have kCap (e : Cell n) : s.le (Kₑ e) K := s.mulMono (major e) (s.refl _)
  have vCap (e : Cell n) : s.le (ns s N ⊗ Kₑ e) V := s.mulMono (s.refl _) (kCap e)
  have pairCap (e : Cell n) (l : Marks) : s.le (P e l) pair := by
    have h := (localEst e).1 l
    rw [times_m,size_mult] at h
    have t' := s.mulMono (s.refl (inv (size ⊗ size))) h
    change s.le (inv (size ⊗ size) ⊗ ((size ⊗ size) ⊗ P e l)) pair at t'
    rwa [←s.mulAssoc,recip _ (mul_live s inv recip A.sizePos A.sizePos),s.oneMul] at t'
  have vel := (step_clock s inv recip m d fits live nextPos).2.1
  have cv (e : Cell n) (l : Marks) : s.le (C e l) s.one :=
    (caps s (p e) _ _ (keys l) (fun i _ => hp e i) (vel ▸ up_left s _ _) (vel ▸ up_left s _ _)).1
  have dv (e : Cell n) (l : Marks) : s.le (D e l) V := by
    have rateCap := s.mulMono (s.refl (weight e)) (quart_mono s (inv_antitone s inv recip fl live margin))
    have feedCap := s.mulMono (le_times s (show d ≤ N by omega) s.one) rateCap
    simpa only [s.mulOne] using s.mulMono (s.trans feedCap (vCap e)) (cv e l)
  apply root_channels s row (board n) f o F B _ _ (fun e => (localEst e).2)
  · intro l
    exact forward_root s x legal z l b g pair V (fun e => P e l) (fun e => C e l) (fun e => D e l)
      (fun e => pairCap e l) (fun e => cv e l) (fun e => dv e l)
  · intro l
    apply adjoint_root s x legal z l _ _ _ _ (fun _ => s.refl _)
    intro e
    unfold availCap
    exact s.mono (s.mulMono (s.mono (kCap e) (s.mulMono (s.refl _) (vCap e))) (s.refl _))
      (s.mono (s.mulMono (vCap e) (s.refl _)) (s.mulMono (s.refl _) (vCap e)))

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.board_step
