import CambioDeMasaDeUnaFuente
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def banderaDeLinea {n} (X : State n) (z : Cell n) (i : Fin 4) (on : Bool) : Prop :=
  if on then X.active i (lines z i)=true else vacant X.physical i (lines z i)
def ambasMarcas {n} (X : State n) (z : Cell n) (j l : Bool) : ℝ :=
  estadoEscalar (banderaDeLinea X z 2 j ∧ banderaDeLinea X z 3 l)

theorem marca_ajena_al_paso {n} (X : State n) (a : Choice n) (fresh : admissible X a)
    (z : Cell n) (i : Fin 4) (on : Bool) (ne : lines z i≠lineOf a i) :
    banderaDeLinea (next X a) z i on ↔ banderaDeLinea X z i on := by
  cases a with
  | fail => cases on <;> rfl
  | virtual v => cases on <;> simp [banderaDeLinea,next,consume,lineOf] at ne ⊢; tauto
  | real c =>
    change lines z i≠lines c i at ne
    cases on
    · exact vacant_insert _ _ fresh _ _ ne.symm
    · simp [banderaDeLinea,next,consume,ne]

theorem coste_de_las_dos_diagonales {n} (X : State n) (a : Choice n) (fresh : admissible X a)
    (j l : Bool) : (∑ z : Cell n,|ambasMarcas (next X a) z j l-ambasMarcas X z j l|)≤2*n := by
  let D (z : Cell n) (i : Fin 4) := estadoEscalar (lines z i=lineOf a i)
  have bound (z : Cell n) : |ambasMarcas (next X a) z j l-ambasMarcas X z j l|≤D z 2+D z 3 := by
    have unit:=distancia_entre_banderas
      (banderaDeLinea (next X a) z 2 j ∧ banderaDeLinea (next X a) z 3 l)
      (banderaDeLinea X z 2 j ∧ banderaDeLinea X z 3 l)
    change |ambasMarcas (next X a) z j l-ambasMarcas X z j l|≤1 at unit
    by_cases h : lines z 2=lineOf a 2
    · have v : D z 2=1 := by simp [D,estadoEscalar,indicator,h]
      rw [v]; exact unit.trans (le_add_of_nonneg_right (escalar_no_negativo _))
    by_cases k : lines z 3=lineOf a 3
    · have v : D z 3=1 := by simp [D,estadoEscalar,indicator,k]
      rw [v]; exact unit.trans (le_add_of_nonneg_left (escalar_no_negativo _))
    have eq:=and_congr (marca_ajena_al_paso X a fresh z 2 j h) (marca_ajena_al_paso X a fresh z 3 l k)
    simp only [ambasMarcas,propext eq,sub_self,abs_zero]
    exact add_nonneg (escalar_no_negativo _) (escalar_no_negativo _)
  apply (Finset.sum_le_sum (fun z _ => bound z)).trans
  rw [Finset.sum_add_distrib]
  exact (add_le_add (masa_de_una_linea (n:=n) 2 _) (masa_de_una_linea (n:=n) 3 _)).trans_eq (by ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.marca_ajena_al_paso
#print axioms ArticuloA.Historias.coste_de_las_dos_diagonales
