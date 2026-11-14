import AdjuntoPonderadoDeLosDieciseisPatrones
import DeLasParejasAlSoporteDelError
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem escalar_no_negativo (P : Prop) : 0≤estadoEscalar P := by unfold estadoEscalar; positivity
theorem escalar_a_lo_sumo_uno (P : Prop) : estadoEscalar P≤1 := by
  by_cases h:P <;> simp [estadoEscalar,indicator,h]

theorem suma_indicador_unico {ι : Type*} [Fintype ι] (P : ι→Prop)
    (uniq : ∀ i j,P i → P j → i=j) : ∑ i,estadoEscalar (P i)≤1 := by
  by_cases ex : ∃ i,P i
  · obtain ⟨i,hi⟩:=ex
    rw [Finset.sum_eq_single i]
    · exact escalar_a_lo_sumo_uno _
    · intro j _ ne; have h : ¬P j := fun hj => ne (uniq j i hj hi)
      simp [estadoEscalar,indicator,h]
    · simp
  · simp only [not_exists] at ex
    simp [estadoEscalar,indicator,ex]

def masaFuente {n} (X : State n) (o : Bool) (e : Cell n) : ℝ :=
  (pesoDeUnaFuente n o:ℝ)*estadoEscalar (estadoFuente X e o)

theorem masaFuente_no_negativa {n} (X : State n) (o : Bool) (e : Cell n) : 0≤masaFuente X o e :=
  mul_nonneg (NNReal.coe_nonneg _) (escalar_no_negativo _)

private theorem fuente_disponible {n} (X : State n) (v : Fin n→Cell n) :
    ∑ i,masaFuente X false (v i)≤1 := by
  by_cases h : n=0
  · subst n; simp
  · have np : (n:ℝ)≠0 := by exact_mod_cast h
    calc
      _ ≤ ∑ _i : Fin n,(n:ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => by
        unfold masaFuente; simpa [pesoDeUnaFuente] using
          mul_le_mul_of_nonneg_left (escalar_a_lo_sumo_uno (estadoFuente X (v i) false))
            (inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) n)))
      _ = 1 := by simp [np]

theorem masa_de_fila_columna {n} {X : State n} (leg : Legal X.physical) (o : Bool) (r : Fin n) :
    (∑ j : Fin n,masaFuente X o (r,j))≤1 ∧ (∑ i : Fin n,masaFuente X o (i,r))≤1 := by
  cases o
  · exact ⟨fuente_disponible X _,fuente_disponible X _⟩
  · simp only [masaFuente,pesoDeUnaFuente,if_true,NNReal.coe_one,one_mul,estadoFuente]
    constructor
    · apply suma_indicador_unico
      intro i j hi hj; by_contra ne
      exact (legal_pair leg hi hj (fun eq => ne (congrArg Prod.snd eq))).1 rfl
    · apply suma_indicador_unico
      intro i j hi hj; by_contra ne
      exact (legal_pair leg hi hj (fun eq => ne (congrArg Prod.fst eq))).2.1 rfl

theorem masa_total_de_fuente {n} {X : State n} (leg : Legal X.physical) (o : Bool) :
    (∑ e : Cell n,masaFuente X o e)≤n := by
  rw [Fintype.sum_prod_type]
  exact (Finset.sum_le_sum (s:=Finset.univ) (fun r _ => (masa_de_fila_columna leg o r).1)).trans_eq (by simp)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.escalar_no_negativo
#print axioms ArticuloA.Historias.escalar_a_lo_sumo_uno
#print axioms ArticuloA.Historias.suma_indicador_unico
#print axioms ArticuloA.Historias.masaFuente_no_negativa
#print axioms ArticuloA.Historias.masa_de_fila_columna
#print axioms ArticuloA.Historias.masa_total_de_fuente
