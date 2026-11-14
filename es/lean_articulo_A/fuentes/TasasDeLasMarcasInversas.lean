import PerdidasDeLasDiezLineas
import EnlaceTasas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def tasaDeMarca {n} (X : State n) (w : ColorWeights ℝ≥0) (v : Vertex) (activa : Bool) :=
  realRate masas X w (·⁻¹) v + (if activa then virtRate masas X w (·⁻¹) v else 0)

private theorem alcanzada {n} {X : State n} {a : Choice n} (ok : allowed X a) (i : Fin 4) (v : ℕ)
    (hit : consumeVertex a i v) : X.active i v=true := by
  have mi : i∈List.finRange 4 := by simp [List.finRange,List.mem_ofFn]; omega
  cases a with
  | fail => exact hit.elim
  | real c => exact hit ▸ List.all_eq_true.mp ok i mi
  | virtual g => exact hit ▸ List.all_eq_true.mp ok i mi

private theorem masa_de_la_linea {n} (X : State n) (w : ColorWeights ℝ≥0) (v : Vertex) (j : Bool)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0) :
    meanN masas (choices masas X w (·⁻¹))
      (fun a => indicator (consumeVertex a v.1 v.2 ∧ (j=true ∨ isReal a)))=tasaDeMarca X w v j := by
  let row:=choices masas X w (·⁻¹)
  have eq (a : Choice n) : indicator (consumeVertex a v.1 v.2 ∧ (j=true ∨ isReal a))=
      indicator (colourAt true v a=true)+(if j then indicator (colourAt false v a=true) else 0) := by
    cases a <;> cases j <;> simp [consumeVertex,isReal,colourAt,hitsVertex,indicator]
  rw [funext eq,mean_plus,real_rate masas X w (·⁻¹) rr vv]
  cases j with
  | true =>
    simp only [if_true,virtual_rate masas X w (·⁻¹) rr vv,tasaDeMarca]
    rfl
  | false =>
    simp only [Bool.false_eq_true,if_false,mean_zero,tasaDeMarca]
    rfl

/-- For physical vacancy the factor that multiplies the real hazard uses the active
mark. The other marks and both source states are evaluated before the choice. -/
theorem intensidad_de_marca {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (i : Fin 4) (j : Bool) (P : Prop) (coh : coherent X)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0) :
    meanN masas (choices masas X w (·⁻¹))
      (fun a => indicator (P ∧ estadoMarca X e f i j ∧ borraMarca e f i j a)) =
    if P ∧ estadoMarca X e f i true then tasaDeMarca X w (lineLabel (corners (e,f)).2 i) j else 0 := by
  let row:=choices masas X w (·⁻¹)
  let v:=lineLabel (corners (e,f)).2 i
  have eq (a : ℝ≥0×Choice n) (mem : a∈row) : (P ∧ estadoMarca X e f i j ∧ borraMarca e f i j a.2) ↔
      (P ∧ estadoMarca X e f i true) ∧ borraMarca e f i j a.2 := by
    constructor
    · rintro ⟨pc,_,hit⟩
      exact ⟨⟨pc,alcanzada (row_allowed masas X w (·⁻¹) a mem) i v.2 hit.1⟩,hit⟩
    · rintro ⟨⟨pc,ac⟩,hit⟩
      refine ⟨pc,?_,hit⟩
      cases j with
      | true => exact ac
      | false => exact active_vacant X coh i _ ac
  by_cases guard : P ∧ estadoMarca X e f i true
  · rw [if_pos guard,←masa_de_la_linea X w _ j rr vv]
    apply mean_eq; intro a ha
    change indicator _=indicator (borraMarca e f i j a.2)
    exact congrArg indicator (propext ((eq a ha).trans ⟨fun x => x.2,fun hit => ⟨guard,hit⟩⟩))
  · rw [if_neg guard]
    apply Eq.trans _ (mean_zero masas row)
    apply mean_eq; intro a ha
    have impossible : ¬(P ∧ estadoMarca X e f i j ∧ borraMarca e f i j a.2) := fun h => guard ((eq a ha).mp h).1
    exact if_neg impossible

theorem dos_tasas_del_destino {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (o b j l : Bool) (coh : coherent X) (rr : total masas (realChoices masas X w)≠0)
    (vv : total masas (virtualChoices masas X w)≠0) :
    let row:=choices masas X w (·⁻¹)
    let rate:=fun i v => tasaDeMarca X w (lineLabel (corners (e,f)).2 i) v
    meanN masas row (fun a => indicator (patronInverso X e f o b j l ∧ borraMarca e f 2 j a))=
      (if patronInverso X e f o b true l then rate 2 j else 0) ∧
    meanN masas row (fun a => indicator (patronInverso X e f o b j l ∧ borraMarca e f 3 l a))=
      (if patronInverso X e f o b j true then rate 3 l else 0) := by
  intro row rate
  constructor
  · have est:=intensidad_de_marca X w e f 2 j (estadoFuente X e o ∧ estadoFuente X f b ∧ estadoMarca X e f 3 l) coh rr vv
    dsimp only [rate,row]
    by_cases ac : patronInverso X e f o b true l
    · rw [if_pos ac]; rw [if_pos (by unfold patronInverso at ac; tauto)] at est
      simpa only [patronInverso,and_assoc,and_left_comm,and_comm] using est
    · rw [if_neg ac]; rw [if_neg (by unfold patronInverso at ac; tauto)] at est
      simpa only [patronInverso,and_assoc,and_left_comm,and_comm] using est
  · have est:=intensidad_de_marca X w e f 3 l (estadoFuente X e o ∧ estadoFuente X f b ∧ estadoMarca X e f 2 j) coh rr vv
    dsimp only [rate,row]
    by_cases ac : patronInverso X e f o b j true
    · rw [if_pos ac]; rw [if_pos (by unfold patronInverso at ac; tauto)] at est
      simpa only [patronInverso,and_assoc,and_left_comm,and_comm] using est
    · rw [if_neg ac]; rw [if_neg (by unfold patronInverso at ac; tauto)] at est
      simpa only [patronInverso,and_assoc,and_left_comm,and_comm] using est

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_tasas_del_destino
