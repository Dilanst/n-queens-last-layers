import VentanaGronwall
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def coeff (p : ι → α) (u : α) : List ι → α
  | [] => s.one
  | i::J => (u ⊗ p i) ⊗ coeff p u J

/-- Sum over all one-index deletions, with the weight of the deleted index. -/
def predecessor (f : List ι → α) (p : ι → α) : List ι → α
  | [] => s.zero
  | i::J => (p i ⊗ f J) ⊞ predecessor (fun L => f (i::L)) p J

def slope (p : ι → α) (u : α) : List ι → α
  | [] => s.zero
  | i::J => (p i ⊗ coeff s p u J) ⊞ ((u ⊗ p i) ⊗ slope p u J)

private theorem pred_scale (f : List ι → α) (p : ι → α) (c : α) (J : List ι) :
    predecessor s (fun L => c ⊗ f L) p J = c ⊗ predecessor s f p J := by
  induction J generalizing f with
  | nil => exact (s.mulZero _).symm
  | cons i J ih =>
    change (p i ⊗ (c ⊗ f J)) ⊞ predecessor s (fun L => c ⊗ f (i::L)) p J =
      c ⊗ ((p i ⊗ f J) ⊞ predecessor s (fun L => f (i::L)) p J)
    rw [ih (fun L => f (i::L)),s.mulAdd]
    congr 1; ac_rfl

theorem slope_deletions (p : ι → α) (u : α) (J : List ι) :
    slope s p u J = predecessor s (coeff s p u) p J := by
  induction J with
  | nil => rfl
  | cons i J ih =>
    change (p i ⊗ coeff s p u J) ⊞ ((u ⊗ p i) ⊗ slope s p u J) =
      (p i ⊗ coeff s p u J) ⊞ predecessor s (fun L => (u ⊗ p i) ⊗ coeff s p u L) p J
    rw [pred_scale,ih]

theorem homogeneous (p : ι → α) (u : α) (J : List ι) :
    u ⊗ slope s p u J = s.times J.length (coeff s p u J) := by
  induction J with
  | nil => exact s.mulZero _
  | cons i J ih =>
    change u ⊗ ((p i ⊗ coeff s p u J) ⊞ ((u ⊗ p i) ⊗ slope s p u J)) =
      ((u ⊗ p i) ⊗ coeff s p u J) ⊞ s.times J.length ((u ⊗ p i) ⊗ coeff s p u J)
    rw [s.mulAdd]
    rw [←s.mulAssoc u (p i)]
    apply congrArg (s.add _)
    calc
      _ = (u ⊗ p i) ⊗ (u ⊗ slope s p u J) := by ac_rfl
      _ = _ := by rw [ih,E2.Regular.times_m,E2.Regular.times_m]; ac_rfl

/-- Product on a chord and its exact nonnegative divided difference. -/
def chord (p : ι → α) (v u : α) : List ι → α
  | [] => s.zero
  | i::J => (p i ⊗ coeff s p v J) ⊞ ((u ⊗ p i) ⊗ chord p v u J)

theorem chord_eq (p : ι → α) (v g : α) (J : List ι) :
    coeff s p (v ⊞ g) J = (coeff s p v J) ⊞ (g ⊗ chord s p v (v ⊞ g) J) := by
  induction J with
  | nil => simp [coeff,chord,s.mulZero,s.comm s.one s.zero,s.zero_add]
  | cons i J ih =>
    change ((v ⊞ g) ⊗ p i) ⊗ coeff s p (v ⊞ g) J =
      ((v ⊗ p i) ⊗ coeff s p v J) ⊞ (g ⊗ ((p i ⊗ coeff s p v J) ⊞ (((v ⊞ g) ⊗ p i) ⊗ chord s p v (v ⊞ g) J)))
    rw [ih,s.mulAdd,s.addMul v g,s.addMul,s.mulAdd g,s.mulAssoc (g) (p i),s.assoc]
    congr 2; ac_rfl

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.homogeneous
#print axioms ArticuloA.Trayectoria.Adjunto.chord_eq
