import SaltoDelCompensador
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular ProfileKernel
variable {α X : Type} (s : ProfileScale α)
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩

theorem mean_within (row : Atoms α X) (f g : X → α) (B : α) (norm : total s row = s.one)
    (h : ∀ i ∈ row, within s (f i.2) (g i.2) B) : within s (avg s row f) (avg s row g) B := by
  have side (f g : X → α) (h : ∀ i ∈ row, s.le (f i.2) (g i.2 ⊞ B)) := avg_mono s row f (fun y => g y ⊞ B) h
  constructor
  · simpa only [avg_plus,avg_constant,norm,s.oneMul] using side f g (fun i hi => (h i hi).1)
  · simpa only [avg_plus,avg_constant,norm,s.oneMul] using side g f (fun i hi => (h i hi).2)

theorem centered (row : Atoms α X) (f g : X → α) (oldF oldG B : α) (norm : total s row = s.one)
    (raw : ∀ i ∈ row, within s (f i.2 ⊞ oldG) (g i.2 ⊞ oldF) B) :
    let positive := fun y => f y ⊞ avg s row g
    let negative := fun y => g y ⊞ avg s row f
    avg s row positive = avg s row negative ∧
      ∀ i ∈ row, within s (positive i.2) (negative i.2) (B ⊞ B) := by
  intro positive negative
  constructor
  · simp only [positive,negative,avg_plus,avg_constant,norm,s.oneMul,s.comm (avg s row g) (avg s row f)]
  · intro i hi
    have both := mean_within s row (fun y => f y ⊞ oldG) (fun y => g y ⊞ oldF) B norm raw
    simp only [avg_plus,avg_constant,norm,s.oneMul] at both
    have flip : within s (avg s row g ⊞ oldF) (avg s row f ⊞ oldG) B := ⟨both.2,both.1⟩
    have v := within_add s (raw i hi) flip
    apply cancel_budget s (c:=oldF ⊞ oldG)
    apply adjust s v <;> dsimp only [positive,negative] <;> ac_rfl

theorem halt_jump (step : Nat → X → Atoms α X) (halt : Nat → X → Bool)
    (F G : Nat → X → α) (u t : Nat) (x : X) (B : α)
    (active : halt t x = false → ∀ i ∈ step t x,
      within s (F (t+1) i.2 ⊞ G t x) (G (t+1) i.2 ⊞ F t x) B) :
    ∀ i ∈ stopped s step halt u (t,x), within s (F i.2.1 i.2.2 ⊞ G t x) (G i.2.1 i.2.2 ⊞ F t x) B := by
  intro i hi
  cases status : halt t x with
  | true =>
    simp only [stopped,status,if_true,point,List.mem_singleton] at hi
    subst i; dsimp; rw [s.comm (G t x) (F t x)]; exact within_self s _ _
  | false =>
    simp only [stopped,status,Bool.false_eq_true,if_false,List.mem_map] at hi
    obtain ⟨j,hj,rfl⟩ := hi
    exact active status j hj

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.centered
#print axioms ArticuloA.Trayectoria.Adjunto.halt_jump
