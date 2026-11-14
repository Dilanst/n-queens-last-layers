import CentradoDeFila
import ConcentracionFija
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

/-- T is deterministic. Both the observable and its clock freeze on exit.
The signed innovation on a full stopped E2 row has zero mean and size ≤ 2B. -/
theorem stopped_innovation {n} (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (pos : ∀ i j : Nat, i+j ≠ 0 → ns s i ⊞ ns s j ≠ s.zero)
    (w : ColorWeights α) (N T : Nat) (early : T < N) (span : N ≤ 2*n)
    (sn : ns s n ≠ s.zero) (zeta M : α) (sz : zeta ≠ s.zero)
    (floor : s.le (ns s n ⊗ zeta) (ns s (N-T)))
    (z : Cell n) (p : Cell n → Fin 4 → α) (pi : Cell n → α)
    (bound : ∀ e, s.le (ns s n ⊗ pi e) M) (hp : ∀ e j, s.le (p e j) s.one)
    (halt : Nat → State n → Bool) (u t : Nat) (x : State n) (good : coherent x) :
    let row := stopped s (kernel s w inv) (freezeAt T halt) u (t,x)
    let val := fun (j : Bool) (v : Nat × State n) => rootPart s inv N (N-v.1) (T-v.1) z p pi v.2 j
    let B := s.times 16 (oneMaskCap s (inv zeta) M)
    let plus := fun y => val false y ⊞ avg s row (val true)
    let minus := fun y => val true y ⊞ avg s row (val false)
    avg s row plus = avg s row minus ∧ ∀ i ∈ row, within s (plus i.2) (minus i.2) (B ⊞ B) := by
  intro row val B plus minus
  have norm := stopped_total s (kernel s w inv) (freezeAt T halt) (kernel_total s w inv recip pos) u (t,x)
  apply centered s row (val false) (val true) (val false (t,x)) (val true (t,x)) B norm
  apply halt_jump s (kernel s w inv) (freezeAt T halt)
    (fun t x => val false (t,x)) (fun t x => val true (t,x)) u t x B
  intro active i hi
  have ht : t < T := by simpa [freezeAt,Bool.or_eq_false_iff] using
    (show decide (T ≤ t) = false from (Bool.or_eq_false_iff.mp active).1)
  let m := N-(t+1)
  let d := T-(t+1)
  have now : N-t=m+1 := by dsimp [m]; omega
  have horizon : T-t=d+1 := by dsimp [d]; omega
  have nz (a : Nat) (ha : 0<a) : ns s a ≠ s.zero := by
    have h := pos 0 a (by omega)
    simpa only [ns,MassScale.times,s.zero_add] using h
  have floor' := s.trans floor (le_times s (show N-T ≤ m by dsimp [m]; omega) s.one)
  have jump := kernel_jump s inv recip w t N m d (by dsimp [d,m]; omega) (by dsimp [m]; omega) span sn
    (nz m (by dsimp [m]; omega)) (nz (m+1) (by omega)) zeta M sz floor' z p pi bound hp x good i hi
  dsimp only [val]; rw [now,horizon]; exact jump

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.stopped_innovation
