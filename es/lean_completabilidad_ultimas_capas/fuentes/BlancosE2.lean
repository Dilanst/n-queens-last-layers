import MargenesTasas
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def cube (z : α) := (z ⊗ z) ⊗ z
def fourth (z : α) := cube s z ⊗ z

/-- q, d, w are the initial quantities divided by n, n, n².
p is the static load, so w*p=q*d. -/
theorem ideal_real (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {T z w q d p : α} (clock : T ≠ s.zero) (base : w ⊗ p = q ⊗ d) :
    (T ⊗ (w ⊗ fourth s z)) ⊗ (inv T ⊗ p) = (q ⊗ z) ⊗ (d ⊗ cube s z) := by
  calc
    _ = (inv T ⊗ T) ⊗ ((w ⊗ p) ⊗ (cube s z ⊗ z)) := by unfold fourth; ac_rfl
    _ = _ := by rw [recip T clock,s.oneMul,base]; ac_rfl

/-- c=N/n, T=c*z, piN=n*pi_e, and the output is n² times k_e. -/
theorem ideal_birth (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {c z w q v piN : α} (live : c ⊗ fourth s z ≠ s.zero) (base : w ⊗ piN = q ⊗ v) :
    ((c ⊗ z) ⊗ (w ⊗ fourth s z)) ⊗ (inv (c ⊗ fourth s z) ⊗ piN) = (q ⊗ z) ⊗ v := by
  calc
    _ = (inv (c ⊗ fourth s z) ⊗ (c ⊗ fourth s z)) ⊗ ((w ⊗ piN) ⊗ z) := by ac_rfl
    _ = _ := by rw [recip _ live,s.oneMul,base]; ac_rfl

theorem ideal_virtual (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {T H z u : α} (clock : T ≠ s.zero) :
    (T ⊗ (H ⊗ z)) ⊗ (inv T ⊗ u) = (H ⊗ z) ⊗ u := by
  calc
    _ = (inv T ⊗ T) ⊗ ((H ⊗ z) ⊗ u) := by ac_rfl
    _ = _ := by rw [recip _ clock,s.oneMul]

theorem complement {t q h q₀ h₀ e : α} (a : s.add q h = t) (b : s.add q₀ h₀ = t)
    (track : within s q q₀ e) : within s h h₀ e := by
  have swap {i j k l : α} (eq : s.add i j = s.add k l) (le : s.le k (s.add i e)) :
      s.le j (s.add l e) := by
    apply s.cancel (c := i)
    rw [s.comm j i,eq,s.comm k l,s.assoc]
    exact s.mono (s.refl _) (by rw [s.comm]; exact le)
  exact ⟨swap (a.trans b.symm) track.2,swap (b.trans a.symm) track.1⟩

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.ideal_birth
