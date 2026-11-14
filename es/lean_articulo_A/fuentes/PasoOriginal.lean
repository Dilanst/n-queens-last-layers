import PresupuestoRegular
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α X : Type} (s : ProfileScale α)

theorem mean_indicator_avg (row : Atoms α X) (P : X → Prop) :
    meanN s row (fun x => indicator (P x)) = avg s row (mark s P) := by
  classical
  induction row with
  | nil => rfl
  | cons a row ih =>
    change s.add (s.times (indicator (P a.2)) a.1) (meanN s row (fun x => indicator (P x))) =
       s.add (s.mul a.1 (mark s P a.2)) (avg s row (mark s P))
    rw [ih]
    by_cases h : P a.2 <;> simp [indicator,mark,h,MassScale.times,s.mulZero,s.mulOne,s.comm _ s.zero,s.zero_add]

theorem expectation_next {n} (x : State n) (t : Nat) (u : ColorWeights α) (inv : α → α)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0) (P : State n → Prop) :
    avg s (kernel s u inv t x) (mark s P) =
    meanN s (choices s x u inv) (fun a => indicator (P (next x a))) := by
  rw [kernel_is_row s x t u inv running remain, avg_push,mean_indicator_avg]
  rfl

theorem choices_total {n} (x : State n) (t : Nat) (u : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (pos : ∀ i j : Nat, i+j ≠ 0 → s.add (s.times i s.one) (s.times j s.one) ≠ s.zero)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0) :
    total s (choices s x u inv) = s.one := by
  have h := kernel_total s u inv recip pos t x
  rw [kernel_is_row s x t u inv running remain] at h
  unfold total at h ⊢
  rw [avg_push] at h
  exact h

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.expectation_next
#print axioms ArticuloA.Trayectoria.E2.choices_total
