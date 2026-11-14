import CotasAdjuntas
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2.Regular Control
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def subsets : List ι → List (List ι)
  | [] => [[]]
  | i::J => subsets J ++ (subsets J).map (i::·)
def parity : List ι → Bool
  | [] => false
  | _::L => !parity L
def part (p : ι → α) (u : α) (b : Bool) (sets : List (List ι)) :=
  s.sum sets (fun J => if parity J = b then coeff s p u J else s.zero)
def prodLines (f : ι → α) : List ι → α
  | [] => s.one
  | i::L => f i ⊗ prodLines f L

theorem part_step (p : ι → α) (u : α) (i : ι) (L : List ι) (b : Bool) :
    part s p u b (subsets (i::L)) = part s p u b (subsets L) ⊞ ((u ⊗ p i) ⊗ part s p u (!b) (subsets L)) := by
  unfold part; rw [subsets,E2.Cart.sum_cat,E2.Cart.sum_map]
  apply congrArg (s.add _)
  have term (J : List ι) : (if parity (i::J)=b then coeff s p u (i::J) else s.zero) =
      (if parity J = !b then coeff s p u J else s.zero) ⊗ (u ⊗ p i) := by
    cases b <;> cases h : parity J <;> simp [parity,coeff,h,s.mulComm,s.mulZero]
  rw [funext term,E2.Cart.sum_scale,s.mulComm]

theorem initial_product (p vacancy : ι → α) (y : α) (L : List ι)
    (factor : ∀ i ∈ L, vacancy i ⊞ (y ⊗ p i) = s.one) :
    part s p y false (subsets L) = prodLines s vacancy L ⊞ part s p y true (subsets L) := by
  induction L with
  | nil => simp [part,subsets,prodLines,coeff,parity,MassScale.sum,s.zero_add,s.comm s.one s.zero]
  | cons i L ih =>
    have old := ih (fun j hj => factor j (by simp [hj]))
    have line := factor i (by simp)
    rw [part_step,part_step]; simp only [Bool.not_false,Bool.not_true,prodLines]
    rw [old,s.mulAdd]
    have eq : prodLines s vacancy L =
        (vacancy i ⊗ prodLines s vacancy L) ⊞ ((y ⊗ p i) ⊗ prodLines s vacancy L) := by
      rw [←s.addMul,line,s.oneMul]
    conv => lhs; arg 1; arg 1; rw [eq]
    ac_rfl

def keys (m : E2.Marks) := (List.finRange 4).filter m
theorem four_positions :
    SizeOn.allMarks.map keys = subsets (List.finRange 4) := by decide
theorem keys_cap (m : E2.Marks) : (keys m).length ≤ 4 := by
  exact Nat.le_trans (List.length_filter_le ..) (by decide)

theorem terminal_magnitude (p : ι → α) (J : List ι) :
    coeff s p s.zero J = if J.isEmpty then s.one else s.zero := by
  cases J with
  | nil => rfl
  | cons i L =>
    change (s.zero ⊗ p i) ⊗ coeff s p s.zero L = s.zero
    rw [s.mulComm s.zero,s.mulZero,s.mulComm s.zero,s.mulZero]

/-- b(0) = (T/N)*pi_e, with w = pi_e*N³. -/
theorem initial_feed (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (N T : Nat) (e : α) (live : ns s N ≠ s.zero) :
    feed s inv (e ⊗ cube s (ns s N)) T N = ratio s inv T N ⊗ e := by
  let m := ns s N
  unfold feed rate ratio quart cube
  calc
    _ = ((inv m ⊗ m) ⊗ ((inv m ⊗ m) ⊗ (inv m ⊗ m))) ⊗ ((inv m ⊗ ns s T) ⊗ e) := by dsimp [m]; ac_rfl
    _ = _ := by rw [recip _ live,s.oneMul,s.oneMul,s.oneMul]

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.initial_product
#print axioms ArticuloA.Trayectoria.Adjunto.four_positions
