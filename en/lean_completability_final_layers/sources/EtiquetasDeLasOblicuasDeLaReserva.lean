import Mathlib.Data.Finset.Card
import LeyIndependienteDeLaReserva
namespace ArticuloA.Historias
open Repair Limites
open scoped BigOperators
noncomputable section
open Classical

abbrev LineaReservable (n : ℕ) := Bool × Fin (2*n+1)

def etiquetaD {n} (e : Cell n) : LineaReservable n :=
    (false,⟨e.1.val+n-e.2.val,by have h:=e.1.isLt; omega⟩)
def etiquetaA {n} (e : Cell n) : LineaReservable n :=
    (true,⟨e.1.val+e.2.val,by have h:=e.1.isLt; have g:=e.2.isLt; omega⟩)

def lineasPropias {n} (e : Cell n) : Finset (LineaReservable n) :={etiquetaD e,etiquetaA e}
def lineasSolicitadas {n} (z e : Cell n) : Finset (LineaReservable n) :=
    lineasPropias (corners (z,e)).1 ∪ lineasPropias (corners (z,e)).2

theorem son_dos_lineas_propias {n} (e : Cell n) : (lineasPropias e).card=2:=by
  have diff : etiquetaD e≠etiquetaA e:=by simp [etiquetaD,etiquetaA]
  simp [lineasPropias,diff]

theorem son_a_lo_sumo_cuatro_marcas {n} (z e : Cell n) : (lineasSolicitadas z e).card≤4:=by
  simpa [lineasSolicitadas,son_dos_lineas_propias] using
    (Finset.card_union_le (lineasPropias (corners (z,e)).1) (lineasPropias (corners (z,e)).2))

theorem propias_y_solicitadas_son_disjuntas {n} (z e : Cell n) (row : z.1≠e.1) (col : z.2≠e.2) :
    Disjoint (lineasSolicitadas z e) (lineasPropias e) := by
  have rr : z.1.val≠e.1.val:=fun h=>row (Fin.ext h)
  have cc : z.2.val≠e.2.val:=fun h=>col (Fin.ext h)
  have hn:=z.2.isLt
  have hn':=e.2.isLt
  rw [Finset.disjoint_left]
  intro i hs hp
  simp only [lineasSolicitadas,lineasPropias,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs hp
  rcases hs with (a|a)|(a|a) <;> rcases hp with b|b <;> subst i <;>
    simp [etiquetaD,etiquetaA,corners,Fin.ext_iff] at b <;> omega

theorem esperanza_de_marca_individual {n} (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (z e : Cell n)
    (row : z.1≠e.1) (col : z.2≠e.2) :
    τ^4*(1-τ)^2≤∑ ω : LineaReservable n→Bool,
      (if acuerdoDeReserva (lineasSolicitadas z e) (lineasPropias e) ω then masaDeReserva τ ω else 0) := by
  rw [probabilidad_de_un_patron_de_reserva _ _ _ (propias_y_solicitadas_son_disjuntas _ _ row col),
    son_dos_lineas_propias]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hτ.1 hτ.2 (son_a_lo_sumo_cuatro_marcas z e)) (sq_nonneg _)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.propias_y_solicitadas_son_disjuntas
#print axioms ArticuloA.Historias.esperanza_de_marca_individual
