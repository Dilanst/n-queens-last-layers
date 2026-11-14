import PiezasDeUnaHistoria
import ReveladoFinito
import ExcepcionesDelRevelado
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria.E2 Revelado
noncomputable section
open Classical
variable {n q : ℕ} (P : Tablero n q) (C : Completion P)

abbrev Candidata (n : ℕ) := Fin 4 → Indice n
def dueno (a : Candidata n) (i : Fin 4) := (cobertura P C i).symm (a i)
def otros (p : Indice n) (a : Candidata n) :=
  (Finset.univ.image (dueno P C a)).erase p
def sinRevelar (p : Indice n) (T : Finset (Indice n)) (a : Candidata n) :=
  ∀ i, dueno P C a i = p ∨ dueno P C a i ∈ T

theorem todos_distintos_de (p : Indice n) (a : Candidata n) :
    otros P C p a ⊆ Finset.univ.erase p := by
  intro j hj
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,Finset.mem_univ _⟩

theorem disponible (p : Indice n) (T : Finset (Indice n)) (a : Candidata n) :
    sinRevelar P C p T a ↔ otros P C p a ⊆ T := by
  constructor
  · intro h j hj
    obtain ⟨ne,im⟩ := Finset.mem_erase.mp hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp im
    exact (h i).resolve_left ne
  · intro sub i
    by_cases eq : dueno P C a i=p
    · exact Or.inl eq
    · exact Or.inr (sub (Finset.mem_erase.mpr ⟨eq,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩))

theorem solo_la_marcada (p : Indice n) (a : Candidata n) :
    otros P C p a=∅ ↔ ∀ i, a i=vertice P C i p := by
  rw [← Finset.subset_empty,← disponible]
  constructor
  · intro h i
    have eq : dueno P C a i=p := (h i).resolve_right (by simp)
    exact ((cobertura P C i).apply_symm_apply (a i)).symm.trans (congrArg (cobertura P C i) eq)
  · intro h i
    left
    exact (cobertura P C i).injective (((cobertura P C i).apply_symm_apply (a i)).trans (h i))

def aristasTotales := (List.finRange (2*n-1)).map (fun j => edgeOf (pieza P C j))
def numeros (a : Candidata n) : Edge := fun i => (a i).val

theorem ordinaria (p : Indice n) (a : Candidata n)
    (h : exceptional (aristasTotales P C) (edgeOf (pieza P C p)) (numeros a) = false) :
    (otros P C p a).card = 4 := by
  have hit (i : Fin 4) : numeros a i = edgeOf (pieza P C (dueno P C a i)) i :=
    congrArg Fin.val ((cobertura P C i).apply_symm_apply (a i)).symm
  have one (i : Fin 4) : dueno P C a i ≠ p := by
    intro eq
    have hs : shares (numeros a) (edgeOf (pieza P C p)) i := beq_iff_eq.mpr (eq ▸ hit i)
    have any := List.any_eq_true.mpr ⟨i,List.mem_finRange i,hs⟩
    simp [exceptional,any] at h
  have two' (i j : Fin 4) (lt : i < j) : dueno P C a i ≠ dueno P C a j := by
    intro eq
    let g := edgeOf (pieza P C (dueno P C a j))
    have hg : g ∈ aristasTotales P C := List.mem_map.mpr ⟨_,List.mem_finRange _,rfl⟩
    have hit' := hit i
    rw [eq] at hit'
    have test : two (numeros a) g := (two_iff _ _).mpr ⟨i,j,lt,hit',hit j⟩
    have yes : (aristasTotales P C).any (two (numeros a)) := List.any_eq_true.mpr ⟨g,hg,test⟩
    simp [exceptional,yes] at h
  have inj : Function.Injective (dueno P C a) := by
    intro i j eq
    rcases lt_trichotomy i j with lt|same|gt
    · exact False.elim (two' i j lt eq)
    · exact same
    · exact False.elim (two' j i gt eq.symm)
  have absent : p ∉ Finset.univ.image (dueno P C a) := by
    intro hp; obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hp; exact one i eq
  rw [otros,Finset.erase_eq_of_not_mem absent,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin]

theorem media_sobre_el_tablero {α : Type*} (E : Finset α) (a : α → Candidata n)
    (p : Indice n) (w : α → ℝ) (z : ℝ) :
    ∑ T ∈ (Finset.univ.erase p).powerset, masa (Finset.univ.erase p) T z *
      (∑ e ∈ E, if sinRevelar P C p T (a e) then w e else 0) =
      ∑ e ∈ E, w e * z^(otros P C p (a e)).card := by
  simp_rw [disponible]
  exact media_normalizador _ E _ (fun e _ => todos_distintos_de P C p (a e)) w z
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ordinaria
#print axioms ArticuloA.Historias.solo_la_marcada
#print axioms ArticuloA.Historias.media_sobre_el_tablero
