import SumaDeLosCanalesInversos
import OperadorIdealDelPatronInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 RealFinita Corte Repair
noncomputable section
open Classical

def paresCompatibles (n : ℕ) : Finset (Mark n) :=
  Finset.univ.filter (fun u => compatible u.1 u.2)

private theorem lista_domina [DecidableEq α] (l : List α) (g : α→ℝ≥0) :
    ∑ u∈l.toFinset,(g u:ℝ)≤(masas.sum l g:ℝ) := by
  induction l with
  | nil => simp [MassScale.sum,masas]
  | cons a l ih =>
    rw [List.toFinset_cons]
    change _≤(↑(g a+masas.sum l g):ℝ)
    rw [NNReal.coe_add]
    by_cases h : a∈l.toFinset
    · rw [Finset.insert_eq_of_mem h]; linarith [show 0≤(g a:ℝ) from (g a).property]
    · rw [Finset.sum_insert h]; exact add_le_add_left ih _

theorem test_sumado_en_el_soporte {n} (X : State n) (o v j l : Bool) (g : Mark n→ℝ≥0) :
    ∑ u∈paresCompatibles n,filtrarTasa (patronInverso X u.1 u.2 o v j l) (g u:ℝ)≤
      (↑(masas.sum (soporteDeParejas X o v j l) g):ℝ) := by
  have sets : (paresCompatibles n).filter (fun u => patronInverso X u.1 u.2 o v j l)=
      (soporteDeParejas X o v j l).toFinset := by
    ext u
    simp only [paresCompatibles,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
    exact (miembros_del_soporte X u.1 u.2 o v j l).symm
  unfold filtrarTasa
  rw [←Finset.sum_filter,sets]; exact lista_domina _ _

theorem cota_de_soporte_ponderada {n} (X : State n) (o v j l : Bool) (g : Mark n→ℝ≥0) (s : ℝ≥0) :
    ∑ u∈paresCompatibles n,(s:ℝ)*filtrarTasa (patronInverso X u.1 u.2 o v j l) (g u:ℝ)≤
      (↑(s*masas.sum (soporteDeParejas X o v j l) g):ℝ) := by
  rw [←Finset.mul_sum,NNReal.coe_mul]
  exact mul_le_mul_of_nonneg_left (test_sumado_en_el_soporte X o v j l g) s.property

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_de_soporte_ponderada
