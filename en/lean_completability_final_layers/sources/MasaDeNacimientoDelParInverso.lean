import NacimientoDeLasFuentesInversas
import FuenteNacimiento
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Repair Corte
noncomputable section
open Classical

private theorem suma_atomica {ι : Type} [DecidableEq ι] (l : List ι) (nd : l.Nodup) (e : ι) (w : ι→ℝ≥0)
    (cond : ι→Prop) :
    masas.sum l (fun i => if e=i ∧ cond i then w i else 0) =
      if e∈l ∧ cond e then w e else 0 := by
  induction l with
  | nil => simp [MassScale.sum,masas]
  | cons a l ih =>
    change (if e=a ∧ cond a then w a else 0) + masas.sum l (fun i => if e=i ∧ cond i then w i else 0) = _
    rw [ih (List.nodup_cons.mp nd).2]
    by_cases eq : e=a
    · subst a; simp [(List.nodup_cons.mp nd).1]
    · simp [eq]

private theorem masa_del_movimiento {n} (X : State n) (w : ColorWeights ℝ≥0) (s : Cell n)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0)
    (P : State n→Prop) :
    meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (bornHere s a ∧ P (next X a))) =
      if E2.available X (lines s)=true ∧ P (next X (.real s)) then realAtom masas X w (·⁻¹) s else 0 := by
  classical
  rw [regular_row masas X w (·⁻¹) rr vv,mean_append,event_on_list,event_on_list]
  have zeroSum {ι} (l : List ι) : masas.sum l (fun _ => 0)=0 := by
    induction l with
    | nil => rfl
    | cons a l ih => change (0:ℝ≥0)+masas.sum l (fun _ => 0)=0; rw [ih,zero_add]
  simp only [bornHere,false_and,and_false,if_false]
  change masas.sum (board n) _ + masas.sum (virtualEdges (2*n-1)) (fun _ => (0:ℝ≥0)) = _
  rw [zeroSum]
  rw [add_zero]
  have rearr (i : Cell n) : (E2.available X (lines i)=true ∧ s=i ∧ P (next X (.real i))) ↔
      s=i ∧ (E2.available X (lines i)=true ∧ P (next X (.real i))) := by tauto
  simp only [rearr]
  convert (suma_atomica (board n) (board_unique n) s (realAtom masas X w (·⁻¹))
    (fun i => E2.available X (lines i)=true ∧ P (next X (.real i)))) using 1
  · apply congrArg (masas.sum (board n)); funext i
    by_cases yes : s=i ∧ E2.available X (lines i)=true ∧ P (next X (.real i)) <;> simp [yes,masas]
  · simp [board_complete s]

theorem masa_de_nacimiento_primera {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0)
    (ok : compatible e f) (coh : coherent X) (v j₂ j₃ : Bool) :
    meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (bornHere e a ∧ patronInverso (next X a) e f true v j₂ j₃)) =
    if patronInverso X e f false v j₂ j₃ then realAtom masas X w (·⁻¹) e else 0 := by
  rw [masa_del_movimiento X w e rr vv (fun Y => patronInverso Y e f true v j₂ j₃)]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨av,yes⟩
    exact (nace_primera_fuente X e f ok (choice_adm coh (.real e) av) av v j₂ j₃).mp yes
  · intro pre
    have av : E2.available X (lines e)=true := pre.1
    exact ⟨av,(nace_primera_fuente X e f ok (choice_adm coh (.real e) av) av v j₂ j₃).mpr pre⟩

theorem masa_de_nacimiento_segunda {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0)
    (ok : compatible e f) (coh : coherent X) (v j₂ j₃ : Bool) :
    meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (bornHere f a ∧ patronInverso (next X a) e f v true j₂ j₃)) =
    if patronInverso X e f v false j₂ j₃ then realAtom masas X w (·⁻¹) f else 0 := by
  rw [masa_del_movimiento X w f rr vv (fun Y => patronInverso Y e f v true j₂ j₃)]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨av,yes⟩
    exact (nace_segunda_fuente X e f ok (choice_adm coh (.real f) av) av v j₂ j₃).mp yes
  · intro pre
    have av : E2.available X (lines f)=true := pre.2.1
    exact ⟨av,(nace_segunda_fuente X e f ok (choice_adm coh (.real f) av) av v j₂ j₃).mpr pre⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_de_nacimiento_primera
#print axioms ArticuloA.Historias.masa_de_nacimiento_segunda
