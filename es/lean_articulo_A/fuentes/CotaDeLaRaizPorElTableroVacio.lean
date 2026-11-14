import EntradaDeSimkinConElConteoCompleto
import RetiradaBinomial
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

theorem capa_vacia_tiene_un_elemento (n : ℕ) : count n 0=1 := by
  classical
  have cero (xs : List (Cell n)) : sumMasks xs (fun _=>0)=0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [sumMasks,ih,add_zero]
  have uno (xs : List (Cell n)) : sumMasks xs (layer 0)=1 := by
    induction xs with
    | nil => simp [sumMasks,layer,pieces,Legal,queens]
    | cons x xs ih =>
      have skip : (fun b : Mask xs=>layer 0 (Mask.skip (x:=x) b))=layer 0 := rfl
      have take : (fun b : Mask xs=>layer 0 (Mask.take (x:=x) b))=(fun _=>0) := by
        funext b; simp [layer,pieces]
      rw [sumMasks,skip,take,cero,ih,add_zero]
  exact uno (board n)

theorem raiz_del_conteo_a_lo_sumo_uno (n : ℕ) : raizDelConteo (fun j=>count j j) n≤1 := by
  by_cases z : n=0
  · simp [z,raizDelConteo]
  have fac : count n n≤n.factorial := by
    simpa [capa_vacia_tiene_un_elemento] using Capas.retirada_binomial n n le_rfl
  have cap : (count n n:ℝ)≤(n:ℝ)^n:=by exact_mod_cast fac.trans (Nat.factorial_le_pow n)
  have np : 0<(n:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero z
  apply (div_le_one np).mpr
  exact (Real.rpow_le_rpow (by positivity) cap (inv_nonneg.mpr np.le)).trans_eq (Real.pow_rpow_inv_natCast np.le z)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.capa_vacia_tiene_un_elemento
#print axioms ArticuloA.Historias.raiz_del_conteo_a_lo_sumo_uno
