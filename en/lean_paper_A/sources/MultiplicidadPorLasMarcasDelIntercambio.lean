import LeyUniformeDelTablero
import Reparaciones
import Mathlib.Data.Fintype.BigOperators
namespace ArticuloA.Historias

noncomputable section
open Repair Limites
open Classical

/-- With the marks fixed, each operation is reversible on the physical board. -/
def aplicarMarcas {n : ℕ} (ms : List (Mark n)) (p : Placement n) : Placement n :=
  ms.foldl (fun u m=>forward m u) p

theorem marcas_determinan_el_original {n : ℕ} (ms : List (Mark n)) :
    Function.Injective (aplicarMarcas ms) := by
  induction ms with
  | nil => exact fun _ _ h=>h
  | cons m ms ih =>
    intro p q eq
    have h : forward m p=forward m q:=ih eq
    simpa using congrArg (backward (corners m)) h

/-- One history chosen per partial placement. Each output is counted once. -/
theorem cardinal_de_los_parciales_completables {n m : ℕ} (buenos : Finset (Placement n))
    (completa : ∀ p ∈ buenos,∃ ms : Fin m→Mark n,aplicarMarcas (List.ofFn ms) p∈nivel n n) :
    buenos.card ≤ count n n * n^(4*m) := by
  choose ms valid using fun p : ↥buenos=>completa p p.property
  let code : ↥buenos → ↥(nivel n n) × (Fin m→Mark n) :=
    fun p=>(⟨aplicarMarcas (List.ofFn (ms p)) p.val,valid p⟩,ms p)
  have inj : Function.Injective code:=by
    intro p q e
    have tags : ms p=ms q:=congrArg Prod.snd e
    have same : aplicarMarcas (List.ofFn (ms p)) p.val=
      aplicarMarcas (List.ofFn (ms q)) q.val:=congrArg (fun z=>(z.1 : Placement n)) e
    rw [tags] at same
    exact Subtype.ext (marcas_determinan_el_original _ same)
  have b:=Fintype.card_le_of_injective code inj
  have markCard : Fintype.card (Mark n)=n^4:=by simp [Mark,Cell]; ring
  simpa only [Fintype.card_prod,Fintype.card_coe,cardinal_nivel,Fintype.card_fun,
    Fintype.card_fin,markCard,pow_mul] using b
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.marcas_determinan_el_original
#print axioms ArticuloA.Historias.cardinal_de_los_parciales_completables
