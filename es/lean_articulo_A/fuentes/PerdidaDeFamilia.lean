import MasaDeColor
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel Regular
variable {α X ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩

theorem avg_plus (L : Atoms α X) (f g : X → α) :
    avg s L (fun x => f x ⊞ g x) = avg s L f ⊞ avg s L g := by
  induction L with
  | nil => exact (s.zero_add _).symm
  | cons i L ih =>
    change (i.1 ⊗ (f i.2 ⊞ g i.2)) ⊞ avg s L (fun x => f x ⊞ g x) = ((i.1 ⊗ f i.2) ⊞ avg s L f) ⊞ ((i.1 ⊗ g i.2) ⊞ avg s L g)
    rw [ih,s.mulAdd]; ac_rfl

theorem avg_sum (L : Atoms α X) (js : List ι) (f : X → ι → α) :
    avg s L (fun x => s.sum js (f x)) = s.sum js (fun j => avg s L (fun x => f x j)) := by
  induction js with
  | nil => exact (avg_constant s L s.zero).trans (s.mulZero _)
  | cons i js ih =>
    change avg s L (fun x => f x i ⊞ s.sum js (f x)) = avg s L (fun x => f x i) ⊞ _
    rw [avg_plus,ih]; rfl

theorem vertex_rate {n} (x : State n) (w : ColorWeights α) (inv : α → α) (v : Vertex)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero) :
    avg s (choices s x w inv) (mark s (fun a => consumeVertex a v.1 v.2)) =
      realRate s x w inv v ⊞ virtRate s x w inv v := by
  rw [←mean_indicator_avg]
  have eq (a : Choice n) : indicator (consumeVertex a v.1 v.2) =
      indicator (colourAt true v a = true) + indicator (colourAt false v a = true) := by
    cases a <;> simp [consumeVertex,indicator,colourAt,hitsVertex]
  rw [funext eq,mean_plus,real_rate s x w inv rr vv,virtual_rate s x w inv rr vv]; rfl

open Classical in
noncomputable def lostWeight {n} (x : State n) (w : ColorWeights α) (f : Fin 4) (a : Choice n) :=
  s.sum (List.range (2*n-1)) (fun j => if x.active f j then
    w f j ⊗ mark s (fun a => consumeVertex a f j) a else s.zero)

theorem family_step {n} (x : State n) (w : ColorWeights α) (f : Fin 4) (a : Choice n) :
    Cart.part s (next x a) w f ⊞ lostWeight s x w f a = Cart.part s x w f := by
  classical
  unfold Cart.part lostWeight
  generalize List.range (2*n-1) = L
  induction L with
  | nil => exact s.zero_add _
  | cons j L ih =>
    change (_ ⊞ s.sum L _) ⊞ (_ ⊞ s.sum L _) = _ ⊞ s.sum L _
    rw [s.assoc,←s.assoc (s.sum L _),s.comm (s.sum L _) _,s.assoc _ (s.sum L _),ih,←s.assoc]
    apply congrArg (fun y => y ⊞ _)
    cases h : x.active f j <;> cases a <;>
      simp [next,consume,consumeVertex,h,mark,s.mulOne,s.mulZero,s.zero_add,s.comm _ s.zero,ne_comm] <;>
      split <;> try simp_all [ne_comm,s.zero_add,s.comm _ s.zero,s.mulOne,s.mulZero]
    all_goals rename_i ne; simp [Ne.symm ne,s.mulZero,s.comm _ s.zero,s.zero_add]

theorem family_rate {n} (x : State n) (w : ColorWeights α) (inv : α → α) (f : Fin 4)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero) :
    avg s (choices s x w inv) (lostWeight s x w f) =
      s.sum (List.range (2*n-1)) (fun j => if x.active f j then
        w f j ⊗ (realRate s x w inv (f,j) ⊞ virtRate s x w inv (f,j)) else s.zero) := by
  unfold lostWeight; rw [avg_sum]; apply congrArg (s.sum _); funext j
  cases h : x.active f j with
  | false => simp only [Bool.false_eq_true,if_false,avg_constant,s.mulZero]
  | true => simp only [if_true]; rw [avg_mul,←vertex_rate s x w inv (f,j) rr vv]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.family_step
#print axioms ArticuloA.Trayectoria.E2.family_rate
