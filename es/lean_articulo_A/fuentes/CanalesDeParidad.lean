import TranspuestaMarcas
import PerdidaDeFamilia
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def masks (h : Bool) := SizeOn.allMarks.filter (fun m => parity (keys m) == h)
def unpack (J : List (Fin 4)) : Marks := fun i => J.contains i
theorem recover (m : Marks) : unpack (keys m) = m := by
  funext i; cases h : m i <;> simp [unpack,keys,List.finRange,List.mem_ofFn,h] <;> omega
def upper (m : Marks) := targets.filter (fun i => !(m i))
def outward (h : Bool) := (masks h).flatMap fun m => (upper m).map
  (fun i => (i,keys m,keys (promote m i)))
def inward (h : Bool) := (masks h).flatMap fun m => (removes (keys m)).map
  (fun e => (e.1,e.2,keys m))
theorem opposite : ∀ h, (outward h).Perm (inward (!h)) := by decide

def cross (p : Fin 4 → α) (Z : Marks → α) (m : Marks) :=
  s.sum (upper m) (fun i => p i ⊗ Z (promote m i))

theorem flux (h : Bool) (p : Fin 4 → α) (C : List (Fin 4) → α) (Z : Marks → α) :
    s.sum (masks h) (fun m => C (keys m) ⊗ cross s p Z m) =
    s.sum (masks (!h)) (fun m => predecessor s C p (keys m) ⊗ Z m) := by
  let w := fun a : Inc => (p a.1 ⊗ C a.2.1) ⊗ Z (unpack a.2.2)
  have perm := permutation_sum s w (opposite h)
  simp only [outward,inward,Cart.sum_flat,Cart.sum_map,w,recover] at perm
  calc
    _ = _ := ?_
    _ = _ := perm
    _ = _ := ?_
  · apply congrArg (s.sum _); funext m
    unfold cross; rw [s.mulComm,←Cart.sum_scale]
    apply congrArg (s.sum _); funext i; ac_rfl
  · apply congrArg (s.sum _); funext m
    rw [pred_sum,Cart.sum_scale]

theorem add_sum (L : List ι) (f g : ι → α) :
    s.sum L (fun i => f i ⊞ g i) = s.sum L f ⊞ s.sum L g := by
  induction L with
  | nil => exact (s.zero_add _).symm
  | cons i L ih =>
    change (f i ⊞ g i) ⊞ s.sum L _ = (f i ⊞ s.sum L f) ⊞ (g i ⊞ s.sum L g)
    rw [ih]; ac_rfl

theorem balance_sum (L : List ι) (f g e : ι → α) (est : ∀ i, within s (f i) (g i) (e i)) :
    within s (s.sum L f) (s.sum L g) (s.sum L e) := by
  induction L with
  | nil => exact within_self s _ _
  | cons i L ih => exact within_add s (est i) ih

theorem cancel_budget {x y c b : α} (h : within s (x ⊞ c) (y ⊞ c) b) : within s x y b := by
  have reorder (u : α) : (u ⊞ c) ⊞ b = (u ⊞ b) ⊞ c := by ac_rfl
  exact ⟨s.cancel (reorder y ▸ h.1),s.cancel (reorder x ▸ h.2)⟩

theorem signed_balance (F O S X B H ef eb : Bool → α)
    (fw : ∀ j, within s ((F j ⊞ S j) ⊞ X j) (B j ⊞ H j) (ef j))
    (bw : ∀ j, within s (O j ⊞ S j) ((B j ⊞ X (!j)) ⊞ H j) (eb j)) :
    within s (F false ⊞ O true) (F true ⊞ O false)
      ((ef false ⊞ ef true) ⊞ (eb false ⊞ eb true)) := by
  have flip {a b e} (v : within s a b e) : within s b a e := ⟨v.2,v.1⟩
  have est := within_add s (within_add s (fw false) (flip (fw true)))
    (within_add s (flip (bw false)) (bw true))
  let c := ((S false ⊞ S true) ⊞ (X false ⊞ X true)) ⊞ ((B false ⊞ B true) ⊞ (H false ⊞ H true))
  apply cancel_budget s (c:=c)
  simp only [Bool.not_false,Bool.not_true] at est
  dsimp only [c]
  apply (show ∀ {a b d f g : α}, a = d → b = f → within s a b g → within s d f g from
    fun ha hb v => ha ▸ hb ▸ v) _ _ est <;> ac_rfl
end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.flux
#print axioms ArticuloA.Trayectoria.Adjunto.signed_balance
