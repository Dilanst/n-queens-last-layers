import FilaEfectiva
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

open Classical in
theorem event_on_list {ι X} (ks : List ι) (live : ι → Bool) (w : ι → α) (tag : ι → X) (P : X → Prop) :
    meanN s (onList ks live w tag) (fun x => indicator (P x)) =
      s.sum ks (fun i => if live i = true ∧ P (tag i) then w i else s.zero) := by
  classical
  induction ks with
  | nil => rfl
  | cons i ks ih =>
    change meanN s (List.map _ ((i::ks).filter live)) _ = s.add _ (s.sum ks _)
    by_cases li : live i = true
    · rw [List.filter_cons_of_pos li,List.map_cons]
      change s.add (s.times (indicator (P (tag i))) (w i)) (meanN s (onList ks live w tag) (fun x => indicator (P x))) = _
      rw [ih]; by_cases h : P (tag i) <;> simp [li,h,indicator,MassScale.times,s.comm _ s.zero,s.zero_add]
    · simpa [onList,List.filter_cons,li,s.zero_add] using ih

private theorem select_one {ι} [DecidableEq ι] (ks : List ι) (nd : ks.Nodup) (e : ι) (v : α) :
    s.sum ks (fun i => if e=i then v else s.zero) = if e ∈ ks then v else s.zero := by
  induction ks with
  | nil => simp [MassScale.sum]
  | cons i ks ih =>
    change s.add _ (s.sum ks _) = _
    rw [ih (List.nodup_cons.mp nd).2]
    by_cases h : e=i
    · subst i; simp [(List.nodup_cons.mp nd).1,s.comm _ s.zero,s.zero_add]
    · simp [h,s.zero_add]

private theorem sum_null {ι} (ks : List ι) : s.sum ks (fun _ => s.zero) = s.zero := by
  induction ks with
  | nil => rfl
  | cons i ks ih => change s.add s.zero (s.sum ks _) = _; rw [s.zero_add,ih]

open Classical in
/-- The exact multiplier of the old available pattern on a regular attempt.
It includes the probability of drawing a real piece. -/
theorem birth_mass {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (z e : Cell n) (m : Marks) :
    meanN s (choices s x u inv) (fun a => indicator (bornHere e a ∧ availPattern x z e m)) =
      if availPattern x z e m then realAtom s x u inv e else s.zero := by
  classical
  rw [regular_row s x u inv rr vv,mean_append,event_on_list,event_on_list]
  simp only [bornHere,false_and,and_false,if_false,sum_null,s.comm _ s.zero,s.zero_add]
  by_cases old : availPattern x z e m
  · rw [if_pos old]
    change s.sum (board n) _ = _
    calc
      _ = s.sum (board n) (fun i => if e=i then realAtom s x u inv e else s.zero) :=
        by apply congrArg (s.sum (board n)); funext i; by_cases hi : e=i
           · subst i; simp [old,old.2.1]
           · simp [hi]
      _ = _ := by rw [select_one s _ (board_unique n),if_pos (board_complete e)]
  · simp [old,sum_null]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.birth_mass
