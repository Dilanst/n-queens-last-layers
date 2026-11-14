import LeyUniformeDelTablero
import GeometriaDeLaInversa
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
open scoped BigOperators
namespace ArticuloA.Historias
open Limites Trayectoria.E2
noncomputable section
open Classical

abbrev Tablero (n q : ℕ) := ↥(nivel n q)
def ocupados {n q} (P : Tablero n q) (i : Fin 4) : Finset ℕ :=
  ((queens P.val).map (fun e => lines e i)).toFinset
def libres {n q} (P : Tablero n q) (i : Fin 4) : Finset ℕ :=
  Finset.range (2*n-1) \ ocupados P i

theorem legal_y_tamano {n q} (P : Tablero n q) : Legal P.val ∧ pieces P.val=q :=
  (Finset.mem_filter.mp P.property).2

theorem cardinal_libres {n q} (P : Tablero n q) (i : Fin 4) :
    (libres P i).card = 2*n-1-q := by
  have H := legal_y_tamano P
  have nd : ((queens P.val).map (fun e => lines e i)).Nodup :=
    List.pairwise_map.mpr (H.1.imp (fun h => (separadas _ _).1 h i))
  have sub : ocupados P i ⊆ Finset.range (2*n-1) := by
    intro a ha
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hr := e.1.isLt; have hc := e.2.isLt
    have cases4 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases4 with rfl|rfl|rfl|rfl <;> simp [lines] <;> omega
  rw [libres,Finset.card_sdiff sub,Finset.card_range,ocupados,
    List.toFinset_card_of_nodup nd, List.length_map,queenLength,H.2]

/-- A virtual edge is indexed by its free row. Its other coordinates are
three bijections on the actual sets of free vertices of the board. -/
abbrev Completion {n q} (P : Tablero n q) :=
  ((libres P 0 : Type) ≃ (libres P 1 : Type)) ×
  ((libres P 0 : Type) ≃ (libres P 2 : Type)) ×
  ((libres P 0 : Type) ≃ (libres P 3 : Type))

def arista {n q} {P : Tablero n q} (C : Completion P) (r : libres P 0) : Edge
  | 0 => r.val
  | 1 => (C.1 r).val
  | 2 => (C.2.1 r).val
  | 3 => (C.2.2 r).val

theorem decodificar {n q} {P : Tablero n q} {C D : Completion P}
    (eq : ∀ r, arista C r = arista D r) : C=D := by
  apply Prod.ext
  · apply Equiv.ext; intro r; exact Subtype.ext (congrFun (eq r) 1)
  · apply Prod.ext
    · apply Equiv.ext; intro r; exact Subtype.ext (congrFun (eq r) 2)
    · apply Equiv.ext; intro r; exact Subtype.ext (congrFun (eq r) 3)

theorem card_completaciones {n q} (P : Tablero n q) :
    Fintype.card (Completion P) = (2*n-1-q).factorial ^ 3 := by
  have B (i : Fin 4) : (libres P 0 : Type) ≃ (libres P i : Type) :=
    (libres P 0).equivFinOfCardEq (cardinal_libres P 0) |>.trans
      ((libres P i).equivFinOfCardEq (cardinal_libres P i)).symm
  simp only [Completion,Fintype.card_prod,Fintype.card_equiv (B 1),Fintype.card_equiv (B 2),
    Fintype.card_equiv (B 3),Fintype.card_coe,cardinal_libres]
  ring

abbrev Decoracion {n q} (P : Tablero n q) := Completion P × Equiv.Perm (Fin (2*n-1))
abbrev Historia (n q : ℕ) := (P : Tablero n q) × Decoracion P
def multiplicidad (n q : ℕ) := (2*n-1-q).factorial^3 * (2*n-1).factorial

theorem card_fibra {n q} (P : Tablero n q) : Fintype.card (Decoracion P) = multiplicidad n q := by
  rw [Fintype.card_prod,card_completaciones,Fintype.card_perm,Fintype.card_fin]; rfl

theorem card_historias (n q : ℕ) :
    Fintype.card (Historia n q) = count n q * multiplicidad n q := by
  rw [Fintype.card_sigma]
  simp only [card_fibra,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe,cardinal_nivel,Nat.cast_id]

def proba (n q : ℕ) : ℝ := (Fintype.card (Historia n q):ℝ)⁻¹

theorem proyeccion (n q : ℕ) (P : Tablero n q) :
    ∑ _ : Decoracion P, proba n q = (count n q:ℝ)⁻¹ := by
  have hx : (multiplicidad n q:ℝ) ≠ 0 := by unfold multiplicidad; positivity
  simp only [Finset.sum_const,Finset.card_univ,card_fibra,nsmul_eq_mul,proba,card_historias,Nat.cast_mul]
  rw [mul_inv_rev,←mul_assoc,mul_inv_cancel₀ hx,one_mul]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.card_historias
#print axioms ArticuloA.Historias.decodificar
#print axioms ArticuloA.Historias.proyeccion
