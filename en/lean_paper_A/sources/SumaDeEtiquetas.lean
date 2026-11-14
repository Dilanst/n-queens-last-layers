import ArbolEtiquetadoDeE2
import TableroAlFinalDeE2
import Mathlib.Algebra.BigOperators.Fin
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}

def etiquetas (H : Historia n q) : List (Choice n) := (lista H).map jugada

private theorem jugadas_distintas : Function.Injective (@jugada n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [jugada]

theorem etiquetas_inyectivas : Function.Injective (@etiquetas n q) := by
  intro H J same
  apply secuencia_inyectiva
  funext t
  have eq := congrArg (fun l : List (Choice n) => l[t.val]?) same
  simpa [etiquetas,lista,List.getElem?_eq_getElem,t.isLt,jugadas_distintas.eq_iff] using eq

private theorem sumar_indices {X : Type} (l : Atoms ℝ≥0 X) (f : X→ℝ≥0) :
    ∑ i : Fin l.length, (l[i.val].1).val*(f l[i.val].2).val=(avg masas l f).val := by
  induction l with
  | nil => simp [avg,masas,Corte.MassScale.sum]
  | cons a l ih =>
    change (∑ i : Fin (l.length+1), ((a::l)[i.val].1).val*(f (a::l)[i.val].2).val)=_
    rw [Fin.sum_univ_succ]
    change a.1.val*(f a.2).val+(∑ i : Fin l.length, _)=a.1.val*(f a.2).val+_
    exact congrArg (a.1.val*(f a.2).val+·) ih

/-- Distinct records give distinct positions in the list. Coincident final states
and repeated atoms elsewhere do not require dividing by their multiplicities. -/
theorem suma_de_atomos {X J : Type} [Fintype J] (l : Atoms ℝ≥0 X) (w : J→ℝ≥0) (r : J→X)
    (inj : Function.Injective r) (mem : ∀ j,(w j,r j)∈l) (f : X→ℝ≥0) (yes : ∀ j,f (r j)=1) :
    ∑ j,(w j).val ≤ (avg masas l f).val := by
  have existsIndex (j : J) : ∃ i : Fin l.length,l[i.val]=(w j,r j) := by
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem (mem j)
    exact ⟨⟨i,hi⟩,eq⟩
  choose index eq using existsIndex
  have inject : Function.Injective index := by
    intro j j' same
    apply inj
    have h := (eq j).symm.trans ((congrArg (fun i : Fin l.length => l[i.val]) same).trans (eq j'))
    exact congrArg Prod.snd h
  let val := fun i : Fin l.length => (l[i.val].1).val*(f l[i.val].2).val
  rw [←sumar_indices]
  change _≤∑ i,val i
  calc
    _ = ∑ j,val (index j) := Finset.sum_congr rfl (fun j _ => by simp [val,eq j,yes])
    _ = ∑ i∈Finset.univ.image index,val i := (Finset.sum_image (fun _ _ _ _ h => inject h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by dsimp [val]; positivity)

def indicadorExitoso (P : Placement n) (x : State n) : ℝ≥0 :=
  if x.failed=false ∧ x.reals=0 ∧ x.virtuals=0 ∧ x.physical=P then 1 else 0

theorem suma_en_la_fibra (P : Tablero n q) (h : ℕ) (level : q=n-h) (w : ColorWeights ℝ≥0)
    (p : Historia n q → ℝ≥0)
    (mem : ∀ d : Decoracion P,
      (p ⟨P,d⟩,etiquetas ⟨P,d⟩,estado ⟨P,d⟩ h (2*n-1))∈arbol w (2*n-1) (initial n h)) :
    ∑ d : Decoracion P,(p ⟨P,d⟩).val ≤
      (avg masas (leaves masas (kernel masas w (·⁻¹)) 0 (2*n-1) (initial n h)) (indicadorExitoso P.val)).val := by
  rw [←proyectar_arbol]
  apply suma_de_atomos _ _ (fun d : Decoracion P => (etiquetas ⟨P,d⟩,estado ⟨P,d⟩ h (2*n-1))) _ mem
  · intro d
    have ok := proyeccion_exitosa (⟨P,d⟩:Historia n q) h level
    exact if_pos ok
  · intro d j eq
    have pair := etiquetas_inyectivas (congrArg Prod.fst eq)
    simpa using pair
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_en_la_fibra
