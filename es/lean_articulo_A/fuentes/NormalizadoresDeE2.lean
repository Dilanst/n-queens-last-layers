import CuotasDelEstado
import CrucesDeLaConfiguracion
import EsperanzaRealFinita
import ProductoVirtual
import Mathlib.Algebra.BigOperators.Ring.Finset
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Limites
noncomputable section
open Classical
variable {n q : ℕ}

def factores (u : Fin 4 → ℕ → ℝ≥0) (i : Fin 4) (j : Indice n) : ℝ := u i j.val

theorem cuatro_pesos (u : Fin 4 → ℕ → ℝ≥0) (a : Candidata n) :
    (weights masas u (numeros a)).val=pesoDe (factores u) a := by
  unfold pesoDe
  rw [Fin.prod_univ_four]
  change (((u 0 (a 0).val:ℝ)*(u 1 (a 1).val:ℝ))*((u 2 (a 2).val:ℝ)*(u 3 (a 3).val:ℝ)))=_
  simp only [factores,mul_assoc]

private theorem suma_positiva {α : Type} [DecidableEq α] (l : List α) (nd : l.Nodup) (f : α→ℝ≥0) :
    (masas.sum l f).val=∑ x∈l.toFinset,(f x:ℝ) := by
  rw [←suma_lista_sin_repetidos l nd]
  induction l with
  | nil => rfl
  | cons x l ih =>
    change (f x:ℝ)+(masas.sum l f:ℝ) = (f x:ℝ)+sumReal.over l _
    exact congrArg ((f x:ℝ)+·) (ih (List.nodup_cons.mp nd).2)

theorem normalizador_real (H : Historia n q) (h : ℕ) (t : Indice n) (u : ColorWeights ℝ≥0) :
    (total masas (realChoices masas (estado H h t.val) u)).val =
      ∑ e : Cell n, if disponibleEn H t (tuplaReal e) then pesoDe (factores u.real) (tuplaReal e) else 0 := by
  change (total masas (onList (board n) _ _ Choice.real)).val=_
  rw [Cart.total_list]
  apply Eq.trans (suma_positiva (board n) (board_unique n) (fun e => if E2.available (estado H h t.val) (lines e) then weights masas u.real (lines e) else 0))
  have all : (board n).toFinset=Finset.univ := by ext e; simp [board_complete]
  rw [all]
  apply Finset.sum_congr rfl; intro e _
  change (↑(if E2.available (estado H h t.val) (numeros (tuplaReal e)) then weights masas u.real (numeros (tuplaReal e)) else (0:ℝ≥0)):ℝ)=_
  by_cases yes : disponibleEn H t (tuplaReal e)
  · rw [if_pos yes,if_pos ((legal_en_el_nucleo H h t _).mpr yes)]
    exact cuatro_pesos u.real (tuplaReal e)
  · rw [if_neg yes,if_neg (fun live => yes ((legal_en_el_nucleo H h t _).mp live))]; rfl

private theorem por_linea (x : State n) (u : Fin 4 → ℕ → ℝ≥0) (i : Fin 4) :
    (Cart.part masas x u i).val =
      ∑ j : Indice n, if x.active i j.val then factores u i j else 0 := by
  unfold Cart.part
  rw [←List.map_coe_finRange,Cart.sum_map]
  apply Eq.trans (suma_positiva _ (List.nodup_finRange _) (fun j : Indice n => if x.active i j.val then u i j.val else 0))
  simp only [List.toFinset_finRange]
  apply Finset.sum_congr rfl; intro j _
  cases bit : x.active i j.val <;> simp [bit,factores,masas]

theorem normalizador_virtual (H : Historia n q) (h : ℕ) (t : Indice n) (u : ColorWeights ℝ≥0) :
    (total masas (virtualChoices masas (estado H h t.val) u.virtual)).val =
      ∑ a : Candidata n, if disponibleEn H t a then pesoDe (factores u.virtual) a else 0 := by
  let x := estado H h t.val
  rw [Cart.normalizer]
  have four : (masas.four (Cart.part masas x u.virtual)).val = ∏ i, (Cart.part masas x u.virtual i).val := by
    rw [Fin.prod_univ_four]; change (_*_)*(_*_)=_; simp [mul_assoc]
  rw [four]; simp_rw [por_linea]; rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl; intro a _
  have iff : disponibleEn H t a ↔ ∀ i, x.active i (a i).val=true := by
    rw [←legal_en_el_nucleo H h t a,E2.available,List.all_eq_true]
    simp [x,numeros]
  by_cases yes : disponibleEn H t a
  · rw [if_pos yes]; exact Finset.prod_congr rfl (fun i _ => if_pos ((iff.mp yes) i))
  · rw [if_neg yes]
    have no := fun all => yes (iff.mpr all)
    obtain ⟨i,hi⟩ := not_forall.mp no
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizador_real
#print axioms ArticuloA.Historias.normalizador_virtual
