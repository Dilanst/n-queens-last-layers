import BlancoDiscretoDelConteoInverso
import SumaEnUnaLineaDelTablero
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
/-- A fixed cell shares at most n cells in each of the four line families. -/
theorem masa_incompatible_de_una_casilla {n} (e : Cell n) :
    (∑ f : Cell n,estadoEscalar (¬compatible e f))≤4*(n:ℝ) := by
  have one (f : Cell n) : estadoEscalar (¬compatible e f)≤
      ∑ i : Fin 4,estadoEscalar (lines f i=lines e i) := by
    by_cases ok : compatible e f
    · simp only [ok,not_true_eq_false,estadoEscalar,indicator,if_false,Nat.cast_zero]
      exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    · have existsLine : ∃ i : Fin 4,lines f i=lines e i := by
        by_contra! diff
        exact ok ((separadas e f).mpr (fun i => Ne.symm (diff i)))
      obtain ⟨i,hit⟩:=existsLine
      have oneAt:=Finset.single_le_sum (f:=fun j : Fin 4 => estadoEscalar (lines f j=lines e j))
        (fun j _ => escalar_no_negativo _) (Finset.mem_univ i)
      simpa [ok,hit,estadoEscalar,indicator] using oneAt
  apply (Finset.sum_le_sum (fun f _ => one f)).trans
  rw [Finset.sum_comm]
  simpa [mul_comm] using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => masa_de_una_linea (n:=n) i (lines e i))

theorem error_de_pares_excluidos {n} (g : Mark n→ℝ) (D : ℝ) (dp : 0≤D) (cap : ∀ u,|g u|≤D) :
    |(∑ u : Mark n,g u)-∑ u∈paresCompatibles n,g u|≤4*(n:ℝ)^3*D := by
  have point (u : Mark n) : |g u-(if compatible u.1 u.2 then g u else 0)|≤
      D*estadoEscalar (¬compatible u.1 u.2) := by
    by_cases ok:compatible u.1 u.2 <;> simp [ok,estadoEscalar,indicator,cap]
  unfold paresCompatibles; rw [Finset.sum_filter,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun u _ => point u)).trans _)
  rw [←Finset.mul_sum,Fintype.sum_prod_type]
  have row:=Finset.sum_le_sum (s:=Finset.univ) (fun e _ => masa_incompatible_de_una_casilla (n:=n) e)
  have bound:=mul_le_mul_of_nonneg_left row dp
  apply bound.trans_eq
  simp [Cell,Fintype.card_prod]; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_incompatible_de_una_casilla
#print axioms ArticuloA.Historias.error_de_pares_excluidos
