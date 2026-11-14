import SaltosDeRegularidad
import MartingalaDeHistorias
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel Adjunto
variable {n α} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

inductive Coord
  | realCount | boardWeight | family (f : Fin 4) | degree (j : Vertex)

noncomputable def observed (inv : α → α) (v : Cell n → α) (w : ColorWeights α) (x : State n) : Coord → α
  | .realCount => ns s x.reals
  | .boardWeight => norm s inv (ns s n) (boardSum s v (fun e => available x (lines e)))
  | .family f => Cart.part s x w f
  | .degree j => auxDegree s x v j

def coordCap (M H : α) : Coord → α
  | .realCount => s.one | .boardWeight => s.times 4 M | .family _ => H | .degree _ => s.times 3 M

theorem coord_kernel (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (sn : ns s n ≠ s.zero) (v : Cell n → α) (w : ColorWeights α) (t : Nat) (x : State n)
    (M H : α) (cap : ∀ e, s.le (v e) M) (line : ∀ f j, j < 2*n-1 → x.active f j → s.le (w f j) H)
    (coord : Coord) (i : α × State n) (hi : i ∈ kernel s w inv t x) :
    within s (observed s inv v w i.2 coord) (observed s inv v w x coord) (coordCap s M H coord) := by
  rcases kernel_child s w inv t x i hi with same | ⟨a,_,eq⟩
  · rw [same]; exact within_self s _ _
  · rw [eq]; cases coord with
    | realCount => exact real_quota_jump s x a
    | boardWeight => exact normalized_board_jump s inv recip sn x a v M cap
    | family f => exact family_jump s x a w f H (line f)
    | degree j => exact degree_jump s x a v M cap j

theorem coord_stopped (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (pos : ∀ i j : Nat, i+j ≠ 0 → ns s i ⊞ ns s j ≠ s.zero) (sn : ns s n ≠ s.zero)
    (v : Cell n → α) (w : ColorWeights α) (halt : Nat → State n → Bool) (u t : Nat) (x : State n)
    (M H : α) (cap : ∀ e, s.le (v e) M)
    (line : halt t x = false → ∀ f j, j < 2*n-1 → x.active f j → s.le (w f j) H) (coord : Coord) :
    let row := stopped s (kernel s w inv) halt u (t,x)
    let f := fun y : Nat × State n => observed s inv v w y.2 coord
    let B := coordCap s M H coord
    ∀ i ∈ row, within s (f i.2) (avg s row f) (B ⊞ B) := by
  intro row f B
  have norm := stopped_total s (kernel s w inv) halt (kernel_total s w inv recip pos) u (t,x)
  have jump : ∀ i ∈ row, within s (f i.2) (f (t,x)) B := by
    intro i hi
    have h := halt_jump s (kernel s w inv) halt (fun _ y => observed s inv v w y coord)
      (fun _ _ => s.zero) u t x B (by
        intro active a mem
        simpa only [s.comm _ s.zero,s.zero_add] using
          coord_kernel s inv recip sn v w t x M H cap (line active) coord a mem) i hi
    simpa only [s.comm _ s.zero,s.zero_add] using h
  have mean := mean_within s row f (fun _ => f (t,x)) B norm jump
  rw [avg_constant,norm,s.oneMul] at mean
  exact fun i hi => within_chain s (jump i hi) ⟨mean.2,mean.1⟩

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.coord_kernel
#print axioms ArticuloA.Trayectoria.E2.Regular.coord_stopped
