import BalanceDelPasoInverso
import TasasDeLasMarcasInversas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

private theorem nacimientos {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n) (o v j l : Bool)
    (ok : compatible e f) (coh : coherent X) (rr : total masas (realChoices masas X w)≠0)
    (vv : total masas (virtualChoices masas X w)≠0) :
    let row:=choices masas X w (·⁻¹)
    meanN masas row (fun a => indicator (naceDelPar X e f o v j l a true))=
      (if o=true ∧ patronInverso X e f false v j l then realAtom masas X w (·⁻¹) e else 0) ∧
    meanN masas row (fun a => indicator (naceDelPar X e f o v j l a false))=
      (if v=true ∧ patronInverso X e f o false j l then realAtom masas X w (·⁻¹) f else 0) := by
  intro row
  constructor
  · cases o
    · simp [naceDelPar,indicator,mean_zero,masas]
    · simp only [eq_self,true_and]
      rw [←masa_de_nacimiento_primera X w e f rr vv ok coh v j l]
      apply mean_eq; intro u mem
      apply congrArg indicator; apply propext
      simp only [naceDelPar,if_true,eq_self,true_and]
      apply and_congr_right; intro born
      cases u with | mk weight mov =>
        have live:=row_allowed masas X w (·⁻¹) (weight,mov) mem
        cases mov with
        | fail => exact born.elim
        | virtual _ => exact born.elim
        | real z => change e=z at born; subst z
                    exact (nace_primera_fuente X e f ok (choice_adm coh _ live) live v j l).symm
  · cases v
    · simp [naceDelPar,indicator,mean_zero,masas]
    · simp only [eq_self,true_and]
      rw [←masa_de_nacimiento_segunda X w e f rr vv ok coh o j l]
      apply mean_eq; intro u mem
      apply congrArg indicator; apply propext
      simp only [naceDelPar,Bool.false_eq_true,if_false,eq_self,true_and]
      apply and_congr_right; intro born
      cases u with | mk weight mov =>
        have live:=row_allowed masas X w (·⁻¹) (weight,mov) mem
        cases mov with
        | fail => exact born.elim
        | virtual _ => exact born.elim
        | real z => change f=z at born; subst z
                    exact (nace_segunda_fuente X e f ok (choice_adm coh _ live) live o j l).symm

/-- The mean is on one original row of the kernel. The base indicator is constant
only after normalization. The sum ranges over ten actual pre-move line labels. -/
theorem deriva_media_del_patron {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n) (o v j l : Bool)
    (ok : compatible e f) (coh : coherent X) (rr : total masas (realChoices masas X w)≠0)
    (vv : total masas (virtualChoices masas X w)≠0) (running : X.failed=false) (rem : X.reals+X.virtuals≠0) :
    let row:=choices masas X w (·⁻¹)
    let U:=patronInverso X e f o v j l
    let hit:=golpeDelPar e f o v j l
    let d:=fun a => deathsOn (diez e f) (hit a)
    meanN masas row (fun a => indicator (patronInverso (next X a) e f o v j l))+
      masas.sum (diez e f) (fun u => meanN masas row (fun a => indicator (U ∧ hit a u))) =
      (indicator U:ℝ≥0)+(if o=true ∧ patronInverso X e f false v j l then realAtom masas X w (·⁻¹) e else 0)+
      (if v=true ∧ patronInverso X e f o false j l then realAtom masas X w (·⁻¹) f else 0)+
      meanN masas row (fun a => indicator U*(d a-1)) := by
  intro row U hit d
  let U':=fun a => indicator (patronInverso (next X a) e f o v j l)
  let B:=fun s a => indicator (naceDelPar X e f o v j l a s)
  have bal:=mean_eq masas row (fun a => U' a+indicator U*d a)
    (fun a => indicator U+B true a+B false a+indicator U*(d a-1))
    (fun a mem => balance_del_paso_inverso X e f o v j l a.2 ok coh (row_allowed masas X w (·⁻¹) a mem))
  simp only [mean_plus] at bal
  have tally : meanN masas row (fun a => indicator U*d a)=
      masas.sum (diez e f) (fun u => meanN masas row (fun a => indicator (U ∧ hit a u))) := by
    have eq (a : Choice n) : indicator U*d a=(diez e f).countP (fun i => decide (U ∧ hit a i)) := by
      by_cases pre : U <;> simp [indicator,d,deathsOn,pre]
    rw [funext eq,mean_count]; apply congrArg (masas.sum (diez e f)); funext i
    apply mean_eq; intro a _; by_cases yes : U ∧ hit a.2 i <;> simp [indicator,yes]
  have norm:=choices_total masas X 0 w (·⁻¹) (fun _ h => inv_mul_cancel₀ h) (by
    intro i j nz; change ns masas i+ns masas j≠0
    rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast nz) running rem
  have old : meanN masas row (fun _ => indicator U)=(indicator U:ℝ≥0) := by
    rw [mean_indicator_avg]
    have eq : mark masas (fun _ : Choice n => U)=(fun _ => (indicator U:ℝ≥0)) := by
      funext a; by_cases h : U <;> simp [mark,indicator,h,masas]
    rw [eq,avg_constant,show total masas row=masas.one from norm]
    exact one_mul _
  have births:=nacimientos X w e f o v j l ok coh rr vv
  change meanN masas row U'+_=_ at bal
  rw [tally,old,show meanN masas row (B true)=_ from births.1,show meanN masas row (B false)=_ from births.2] at bal
  exact bal
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_media_del_patron
