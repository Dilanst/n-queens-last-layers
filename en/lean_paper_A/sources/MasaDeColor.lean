import VentanaGronwall
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel Regular
variable {α X : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem avg_agree (L : Atoms α X) (f g : X → α) (agree : ∀ i ∈ L, f i.2 = g i.2) :
    avg s L f = avg s L g := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change (_ ⊗ f i.2) ⊞ avg s L f = (_ ⊗ g i.2) ⊞ avg s L g
    rw [agree i (by simp),ih (fun k hk => agree k (by simp [hk]))]

theorem avg_constant (L : Atoms α X) (v : α) : avg s L (fun _ => v) = total s L ⊗ v := by
  induction L with
  | nil => rw [s.mulComm]; exact (s.mulZero _).symm
  | cons i L ih =>
    change (i.1 ⊗ v) ⊞ avg s L (fun _ => v) = ((i.1 ⊗ s.one) ⊞ total s L) ⊗ v
    rw [ih,s.mulOne,s.addMul]

theorem colour_drift {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (wr : total s (realChoices s x w) ≠ s.zero) (wv : total s (virtualChoices s x w) ≠ s.zero) :
    meanN s (choices s x w inv) (fun a => x.reals-(next x a).reals) = quota s x inv x.reals := by
  classical
  by_cases empty : x.reals=0
  · have h : (fun a : Choice n => x.reals-(next x a).reals) = fun _ => 0 := by funext a; simp [empty]
    rw [h,mean_zero]; simp [quota,empty,MassScale.times,s.mulZero]
  have represent : (fun a : Choice n => x.reals-(next x a).reals) = fun a => indicator (isReal a) := by
    funext a; cases a <;> simp [next,isReal,indicator] <;> omega
  rw [represent,mean_indicator_avg,choices,mixture,avg_append,avg_scale,avg_scale]
  have regular {L : Atoms α (Choice n)} (pos : total s L ≠ s.zero) (c : α)
      (same : ∀ i ∈ L, mark s isReal i.2 = c) :
      avg s (choose s L .fail inv) (mark s isReal) = c := by
    rw [avg_agree s _ _ (fun _ => c) (by
      intro i hi; unfold choose at hi; rw [if_neg pos] at hi
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact same j hj),avg_constant,choose_total s _ _ _ recip,s.oneMul]
  rw [regular wr s.one (by intro i hi; obtain ⟨e,_,rfl⟩ := List.mem_map.mp hi; simp [mark,isReal]),
    regular wv s.zero (by intro i hi; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hi; simp [mark,isReal]),
    s.mulOne,s.mulZero,s.comm _ s.zero,s.zero_add]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.colour_drift
