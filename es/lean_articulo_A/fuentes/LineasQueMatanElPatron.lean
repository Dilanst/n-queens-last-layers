import PerdidasDeLasDiezLineas
import BorradosYNacimientosSumados
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair
noncomputable section

/-- A hit is recorded on an actual line of this pair. Occupied sources
persist, physical vacancy only responds to real choices. -/
def golpeDelPar {n} (e f : Cell n) (o v j l : Bool) (a : Choice n) (w : Vertex) : Prop :=
  consumeVertex a w.1 w.2 ∧
    ((o=false ∧ ∃ i,w=lineLabel e i) ∨ (v=false ∧ ∃ i,w=lineLabel f i) ∨
     (w=lineLabel (corners (e,f)).2 2 ∧ (j=true ∨ isReal a)) ∨
     (w=lineLabel (corners (e,f)).2 3 ∧ (l=true ∨ isReal a)))

private theorem etiqueta_de_fuente {n} (e f : Cell n) (i : Fin 4) :
    lineLabel e i ∈ diez e f ∧ lineLabel f i ∈ diez e f := by
  fin_cases i <;> simp [diez]

theorem supervivencia_equivale_a_cero {n} (e f : Cell n) (o v j l : Bool) (a : Choice n) :
    sobreviveElPar e f o v j l a ↔ deathsOn (diez e f) (golpeDelPar e f o v j l a)=0 := by
  classical
  simp only [deathsOn,List.countP_eq_zero,decide_eq_true_eq]
  constructor
  · rintro ⟨le₁,le₂,tr₂,tr₃⟩ w _ ⟨hit,src|src|dst|dst⟩
    · obtain ⟨off,i,rfl⟩:=src
      exact (le₁.resolve_left (by simp [off])) i hit
    · obtain ⟨off,i,rfl⟩:=src
      exact (le₂.resolve_left (by simp [off])) i hit
    · obtain ⟨rfl,real⟩:=dst
      exact tr₂ ⟨hit,real⟩
    · obtain ⟨rfl,real⟩:=dst
      exact tr₃ ⟨hit,real⟩
  · intro none
    refine ⟨?_,?_,?_,?_⟩
    · cases o
      · right; intro i con
        exact none _ (etiqueta_de_fuente e f i).1 ⟨con,Or.inl ⟨rfl,i,rfl⟩⟩
      · left; rfl
    · cases v
      · right; intro i con
        exact none _ (etiqueta_de_fuente e f i).2 ⟨con,Or.inr (Or.inl ⟨rfl,i,rfl⟩)⟩
      · left; rfl
    · rintro ⟨con,real⟩
      exact none _ (by simp [diez] : lineLabel (corners (e,f)).2 2∈diez e f)
        ⟨con,Or.inr (Or.inr (Or.inl ⟨rfl,real⟩))⟩
    · rintro ⟨con,real⟩
      exact none _ (by simp [diez] : lineLabel (corners (e,f)).2 3∈diez e f)
        ⟨con,Or.inr (Or.inr (Or.inr ⟨rfl,real⟩))⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.supervivencia_equivale_a_cero
