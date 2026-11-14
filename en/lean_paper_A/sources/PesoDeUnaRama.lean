import DuenosDelNormalizador
import OrdenDeHistorias
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
variable {n q : ℕ}
def tuplaReal (e : Cell n) : Candidata n := fun i => ⟨lines e i,rango e i⟩
def tupla (H : Historia n q) (t : Indice n) : Candidata n :=
  fun i => vertice H.1 H.2.1 i (H.2.2 t)
def pesoDe (u : Fin 4 → Indice n → ℝ) (a : Candidata n) := ∏ i, u i (a i)
def peso (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (t : Indice n) :=
  pesoDe u (tupla H t)

theorem producto_de_pesos (H : Historia n q) (u : Fin 4 → Indice n → ℝ) :
    ∏ t, peso H u t = ∏ i, ∏ j, u i j := by
  unfold peso pesoDe tupla
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact (H.2.2.trans (cobertura H.1 H.2.1 i)).prod_comp (u i)

def posteriores (H : Historia n q) (t : Indice n) :=
  (Finset.univ.filter (fun s : Indice n => t<s)).image H.2.2
def disponibleEn (H : Historia n q) (t : Indice n) (a : Candidata n) :=
  sinRevelar H.1 H.2.1 (H.2.2 t) (posteriores H t) a

theorem activa_antes_del_paso (H : Historia n q) (t : Indice n) (a : Candidata n) :
    disponibleEn H t a ↔ ∀ i s, s<t → tupla H s i ≠ a i := by
  constructor
  · intro h i s lt eq
    have own : dueno H.1 H.2.1 a i = H.2.2 s := by
      apply (cobertura H.1 H.2.1 i).injective
      exact ((cobertura H.1 H.2.1 i).apply_symm_apply (a i)).trans eq.symm
    rcases h i with same|later
    · exact (ne_of_lt lt) (H.2.2.injective (own.symm.trans same))
    · obtain ⟨v,hv,eqv⟩ := Finset.mem_image.mp later
      have greater := (Finset.mem_filter.mp hv).2
      have same := H.2.2.injective (eqv.trans own)
      subst v; exact (not_lt_of_ge (le_of_lt lt)) greater
  · intro h i
    let s := H.2.2.symm (dueno H.1 H.2.1 a i)
    have own : H.2.2 s = dueno H.1 H.2.1 a i := H.2.2.apply_symm_apply _
    rcases lt_trichotomy s t with lt|same|gt
    · have hit : tupla H s i=a i :=
        (congrArg (cobertura H.1 H.2.1 i) own).trans ((cobertura H.1 H.2.1 i).apply_symm_apply _)
      exact False.elim (h i s lt hit)
    · exact Or.inl (own.symm.trans (congrArg H.2.2 same))
    · exact Or.inr (Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,gt⟩,own⟩)

theorem pieza_disponible (H : Historia n q) (t : Indice n) : disponibleEn H t (tupla H t) := by
  intro i
  exact Or.inl ((cobertura H.1 H.2.1 i).symm_apply_apply (H.2.2 t))

def normalizador (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (t : Indice n) : ℝ :=
  match secuencia H t with
  | .real _ => ∑ e : Cell n, if disponibleEn H t (tuplaReal e) then pesoDe u (tuplaReal e) else 0
  | .virtual _ => ∑ a : Candidata n, if disponibleEn H t a then pesoDe u a else 0

theorem positivo (H : Historia n q) (u : Fin 4 → Indice n → ℝ) (hu : ∀ i j,0<u i j) (t : Indice n) :
    0 < normalizador H u t := by
  have positive (a : Candidata n) : 0 < pesoDe u a := Finset.prod_pos (fun i _ => hu i _)
  have nn (a : Candidata n) : 0 ≤ (if disponibleEn H t a then pesoDe u a else 0) := by
    split_ifs <;> first | exact (positive _).le | rfl
  cases eq : secuencia H t with
  | real e =>
    have same : tuplaReal e=tupla H t := by
      funext i; apply Fin.ext
      exact (congrArg (fun j => edgeOf j i) eq).symm
    rw [normalizador,eq]
    apply Finset.sum_pos' (fun e _ => nn (tuplaReal e))
    exact ⟨e,Finset.mem_univ _,by rw [same,if_pos (pieza_disponible H t)]; exact positive _⟩
  | virtual a =>
    rw [normalizador,eq]
    apply Finset.sum_pos' (fun e _ => nn e)
    exact ⟨tupla H t,Finset.mem_univ _,by rw [if_pos (pieza_disponible H t)]; exact positive _⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.activa_antes_del_paso
#print axioms ArticuloA.Historias.positivo
#print axioms ArticuloA.Historias.producto_de_pesos
