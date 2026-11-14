import AtomoDeLaHistoria
import SumaDeEtiquetas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}

def pesoCamino (H : Historia n q) (h : ℕ) (u : ColorWeights ℝ≥0) :=
  ∏ i,probPaso (estado H h i.val) u (secuencia H i)

theorem camino_completo (H : Historia n q) (h : ℕ) (lev : q=n-h) (u : ColorWeights ℝ≥0)
    (nz : ∀ i : Indice n,denominador (estado H h i.val) u (secuencia H i)≠0) :
    (pesoCamino H h u,etiquetas H,estado H h (2*n-1))∈arbol u (2*n-1) (initial n h) := by
  let N:=2*n-1
  let W := fun i : Indice n => probPaso (estado H h i.val) u (secuencia H i)
  let label := fun i : Indice n => jugada (secuencia H i)
  let xs := List.finRange N
  have len : xs.length=N := List.length_finRange
  have it (m t : ℕ) (talla : t+m=N) :
      ((((xs.drop t).map W).prod, (xs.drop t).map label, estado H h N) ∈ arbol u m (estado H h t)) := by
    induction m generalizing t with
    | zero =>
      have time : t=N := by omega
      subst t; rw [List.drop_eq_nil_of_le len.le]
      simp [arbol,point,masas]
    | succ m ih =>
      have lt : t<N := by omega
      have idx : t<xs.length := by omega
      rw [List.drop_eq_getElem_cons idx,List.map_cons,List.prod_cons,List.map_cons]
      have head : xs[t]=⟨t,lt⟩ := by simp [xs]
      rw [head]
      exact concatenar_rama u m _ _ _ _ _ _ _ (atomo_de_un_paso H h lev u ⟨t,lt⟩ (nz _)) (ih (t+1) (by omega))
  have answer := it N 0 (Nat.zero_add _)
  simpa only [List.drop_zero,xs,W,label,N,←Fin.prod_univ_def,etiquetas,lista,List.map_map,
    Function.comp_def,pesoCamino,estado] using answer

theorem peso_como_producto (H : Historia n q) (h : ℕ) (lev : q=n-h) (u : ColorWeights ℝ≥0) :
    (pesoCamino H h u).val = masaPalabra n q * ∏ i,
      (elegido u (secuencia H i)).val/(denominador (estado H h i.val) u (secuencia H i)).val := by
  rw [←cuotas_reales_del_camino H h lev,←Finset.prod_mul_distrib]
  unfold pesoCamino
  apply Eq.trans (NNReal.coe_prod (s:=Finset.univ) (f:=fun i : Indice n => probPaso (estado H h i.val) u (secuencia H i)))
  apply Finset.prod_congr rfl; intro i _
  simp [probPaso,div_eq_mul_inv,mul_comm]

theorem peso_fisico_comun (H : Historia n q) (h : ℕ) (lev : q=n-h) (u : Fin 4 → ℕ → ℝ≥0) :
    (pesoCamino H h (sameColors u)).val=masaRamaCon H (factores u) (fun J i => normalizador J (factores u) i) := by
  rw [peso_como_producto H h lev]; simp only [masaRamaCon,peso_comun,masa_comun]

theorem peso_fisico_en_lleno (H : Historia n n) (u : Fin 4 → ℕ → ℝ≥0) :
    (pesoCamino H 0 (coloresLlenos n u)).val=ramaCero H (factores u) := by
  rw [peso_como_producto H 0 (by omega)]; simp only [ramaCero,peso_en_lleno,masa_en_lleno]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.camino_completo
#print axioms ArticuloA.Historias.peso_fisico_en_lleno
