import PolinomiosAdjuntos
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def second (p : ι → α) (v u : α) : List ι → α
  | [] => s.zero
  | i::J => (p i ⊗ chord s p v u J) ⊞ ((v ⊗ p i) ⊗ second p v u J)

def pairsN : Nat → Nat
  | 0 => 0
  | j+1 => j + pairsN j

theorem chord_order (p : ι → α) (v g : α) (J : List ι) :
    chord s p v (v ⊞ g) J = (slope s p v J) ⊞ (g ⊗ second s p v (v ⊞ g) J) := by
  induction J with
  | nil => simp [chord,slope,second,s.mulZero,s.zero_add]
  | cons i J ih =>
    change (p i ⊗ coeff s p v J) ⊞ (((v ⊞ g) ⊗ p i) ⊗ chord s p v (v ⊞ g) J) =
      ((p i ⊗ coeff s p v J) ⊞ ((v ⊗ p i) ⊗ slope s p v J)) ⊞
      (g ⊗ ((p i ⊗ chord s p v (v ⊞ g) J) ⊞ ((v ⊗ p i) ⊗ second s p v (v ⊞ g) J)))
    rw [s.addMul v g,s.addMul,s.assoc,s.mulAdd g]
    apply congrArg (s.add _)
    conv => lhs; arg 2; rw [s.mulAssoc]
    conv => lhs; arg 1; arg 2; rw [ih]
    rw [s.mulAdd,s.assoc]; apply congrArg (s.add _)
    rw [s.comm]; congr 1; ac_rfl

theorem expansion (p : ι → α) (v g : α) (J : List ι) :
    coeff s p (v ⊞ g) J = coeff s p v J ⊞
      ((g ⊗ slope s p v J) ⊞ ((g ⊗ g) ⊗ second s p v (v ⊞ g) J)) := by
  rw [chord_eq,chord_order,s.mulAdd,s.mulAssoc]

theorem caps (p : ι → α) (v u : α) (J : List ι)
    (hp : ∀ i ∈ J, p i ≼ s.one) (hv : v ≼ s.one) (hu : u ≼ s.one) :
    coeff s p v J ≼ s.one ∧ chord s p v u J ≼ s.times J.length s.one ∧
    second s p v u J ≼ s.times (pairsN J.length) s.one := by
  induction J with
  | nil => exact ⟨s.refl _,s.refl _,s.refl _⟩
  | cons i J ih =>
    have hi := hp i (by simp)
    obtain ⟨a,b,c⟩ := ih (fun k hk => hp k (by simp [hk]))
    have small (v : α) (low : v ≼ s.one) : (v ⊗ p i) ≼ s.one := by
      simpa only [s.oneMul] using s.mulMono low hi
    have left := s.mulMono hi a
    have step := s.mulMono (small u hu) b
    have pair := s.mono (s.mulMono hi b) (s.mulMono (small v hv) c)
    refine ⟨?_,?_,?_⟩
    · simpa only [coeff,s.oneMul] using s.mulMono (small v hv) a
    · simpa only [chord,s.oneMul,List.length_cons,MassScale.times] using s.mono left step
    · simpa only [second,s.oneMul,List.length_cons,pairsN,plus_times] using pair

theorem slope_cap (p : ι → α) (u : α) (J : List ι) (hp : ∀ i ∈ J, p i ≼ s.one)
    (hu : u ≼ s.one) : slope s p u J ≼ s.times J.length s.one := by
  have eq : chord s p u u J = slope s p u J := by
    induction J with | nil => rfl | cons i J ih => simp only [chord,slope,ih (fun k hk => hp k (by simp [hk]))]
  rw [←eq]; exact (caps s p u u J hp hu hu).2.1

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.expansion
#print axioms ArticuloA.Trayectoria.Adjunto.caps
