import InnovacionDelCompensador
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2 ProfileKernel
variable {α X : Type} (s : ProfileScale α)
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩

structure HistoryBook (X α : Type) where
  state : X
  pos : α
  neg : α
  driftPos : α
  driftNeg : α

variable (step : Nat → X → Atoms α X) (F G : Nat → X → α)

def record (t : Nat) (h : HistoryBook X α) (y : X) : HistoryBook X α :=
  let row := step t h.state
  let f := avg s row (F (t+1))
  let g := avg s row (G (t+1))
  ⟨y,h.pos ⊞ (F (t+1) y ⊞ g), h.neg ⊞ (G (t+1) y ⊞ f),
    h.driftPos ⊞ (f ⊞ G t h.state),h.driftNeg ⊞ (g ⊞ F t h.state)⟩

def historyRow (t : Nat) (h : HistoryBook X α) : Atoms α (HistoryBook X α) :=
  (step t h.state).map (fun i => (i.1,record s step F G t h i.2))

def balanced (t : Nat) (h : HistoryBook X α) (f₀ g₀ : α) :=
  ((F t h.state ⊞ g₀) ⊞ h.neg) ⊞ h.driftNeg = ((G t h.state ⊞ f₀) ⊞ h.pos) ⊞ h.driftPos

theorem record_balance {t : Nat} {h : HistoryBook X α} {f₀ g₀ : α} (start : balanced s F G t h f₀ g₀) (y : X) :
    balanced s F G (t+1) (record s step F G t h y) f₀ g₀ := by
  let extra := (F (t+1) y ⊞ G (t+1) y) ⊞ (avg s (step t h.state) (F (t+1)) ⊞ avg s (step t h.state) (G (t+1)))
  have eq := congrArg (fun u => u ⊞ extra) start
  unfold balanced at start ⊢; dsimp only [record,extra] at eq ⊢
  calc
    _ = (((F t h.state ⊞ g₀) ⊞ h.neg) ⊞ h.driftNeg) ⊞ extra := by dsimp [extra]; ac_rfl
    _ = _ := eq
    _ = _ := by ac_rfl

theorem leaf_balance (t m : Nat) (h : HistoryBook X α) (f₀ g₀ : α)
    (start : balanced s F G t h f₀ g₀) : ∀ i ∈ leaves s (historyRow s step F G) t m h,
      balanced s F G (t+m) i.2 f₀ g₀ := by
  induction m generalizing t h with
  | zero => intro i hi; obtain rfl := List.mem_singleton.mp hi; exact start
  | succ m ih =>
    intro i hi; obtain ⟨j,jh,km⟩ := List.mem_flatMap.mp hi
    obtain ⟨k,mem,rfl⟩ := List.mem_map.mp km
    obtain ⟨a,_,eq⟩ := List.mem_map.mp jh
    rw [show t+(m+1) = (t+1)+m by omega]
    exact ih (t+1) j.2 (eq ▸ record_balance s step F G start a.2) k mem

def gain (t : Nat) : Nat → X → α
  | 0, _ => s.zero
  | m+1, x =>
    let row := step t x
    (avg s row (F (t+1)) ⊞ avg s row (G (t+1))) ⊞ avg s row (gain (t+1) m)

theorem mean_book (norm : ∀ t x, total s (step t x) = s.one) (t m : Nat) (h : HistoryBook X α)
    (odd : Bool) :
    let side := fun (b : HistoryBook X α) => if odd then b.neg else b.pos
    avg s (leaves s (historyRow s step F G) t m h) side = side h ⊞ gain s step F G t m h.state := by
  intro side
  induction m generalizing t h with
  | zero => rw [leaves,avg_point,gain,s.comm _ s.zero,s.zero_add]
  | succ m ih =>
    rw [leaves,avg_bind]
    have changeFuture := funext (fun b : HistoryBook X α => ih (t+1) b)
    rw [changeFuture]; unfold historyRow; rw [avg_push]
    cases odd <;> simp only [side,record,gain,Bool.false_eq_true,if_true,if_false,avg_plus,avg_constant,norm,s.oneMul] <;> ac_rfl
end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.leaf_balance
#print axioms ArticuloA.Trayectoria.Adjunto.mean_book
