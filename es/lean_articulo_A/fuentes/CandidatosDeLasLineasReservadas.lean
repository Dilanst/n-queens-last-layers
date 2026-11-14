import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CompletacionPorReparacionesSucesivas
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical

def llaveDeLinea {n : ℕ} : Fin 4→Cell n→ℤ
  | 0,c => c.1.val
  | 1,c => c.2.val
  | 2,c => (c.1.val:ℤ)-c.2.val
  | 3,c => (c.1.val:ℤ)+c.2.val

theorem compatible_iff_llaves {n} (a b : Cell n) :
    compatible a b ↔ ∀ i,llaveDeLinea i a≠llaveDeLinea i b := by
  constructor
  · rintro ⟨r,c,d,s⟩ i
    fin_cases i <;> simp [llaveDeLinea] <;> omega
  · intro h
    have r:=h 0; have c:=h 1; have d:=h 2; have s:=h 3
    simp [llaveDeLinea] at r c d s
    exact ⟨fun e=>r (congrArg Fin.val e),fun e=>c (congrArg Fin.val e),by omega,by omega⟩

def candidatasDeReserva {n} (p : Placement n) (z : Cell n) (D A : ℤ→Prop) : Finset (Cell n) :=
  (soporteFisico p).filter (fun e=>∀ y∈([ (corners (z,e)).1,(corners (z,e)).2 ] : List (Cell n)),
    D (llaveDeLinea 2 y) ∧ A (llaveDeLinea 3 y))

theorem candidatas_menos_cuatro {n} {p : Placement n} (legal : Legal p) (z : Cell n) (D A : ℤ→Prop)
    (evita : ∀ e ∈ queens p,¬D (llaveDeLinea 2 e) ∧ ¬A (llaveDeLinea 3 e)) :
    (candidatasDeReserva p z D A).card≤physicalCount p z+4 := by
  classical
  let bad (i : Fin 4):=(soporteFisico p).filter (fun e=>llaveDeLinea i e=llaveDeLinea i z)
  have single (i : Fin 4) : (bad i).card≤1:=by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨oa,ka⟩:=Finset.mem_filter.mp ha
    obtain ⟨ob,kb⟩:=Finset.mem_filter.mp hb
    by_contra ne
    have cmp:=legal_pair legal (by simpa [soporteFisico] using oa) (by simpa [soporteFisico] using ob) ne
    exact (compatible_iff_llaves _ _).mp cmp i (ka.trans kb.symm)
  let U := Finset.univ.biUnion bad
  have cap : U.card≤4:=calc
    _ ≤ ∑ i : Fin 4,(bad i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 4,1 := Finset.sum_le_sum (fun i _=>single i)
    _ = 4 := by simp
  let good:=(board n).toFinset.filter (Candidate p z)
  have sub : candidatasDeReserva p z D A ⊆ good ∪ U := by
    intro e he
    obtain ⟨old,marked⟩:=Finset.mem_filter.mp he
    by_cases ok : compatible z e
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      have clear (y : Cell n) (dy : D (llaveDeLinea 2 y)) (ay : A (llaveDeLinea 3 y)) :
          freeDiagonals p y:=by
        intro v hv
        obtain ⟨d,a⟩:=evita _ hv
        have nd : llaveDeLinea 2 v≠llaveDeLinea 2 y:=fun e=>d (e ▸ dy)
        have na : llaveDeLinea 3 v≠llaveDeLinea 3 y:=fun e=>a (e ▸ ay)
        simp [llaveDeLinea] at nd na
        exact ⟨by omega,by omega⟩
      have c₁:=marked (corners (z,e)).1 (by simp)
      have c₂:=marked (corners (z,e)).2 (by simp)
      exact ⟨by simp [board_complete],by simpa [soporteFisico] using old,
        ⟨ok.1,ok.2.1.symm,ok.2.2.2,ok.2.2.1⟩,clear _ c₁.1 c₁.2,clear _ c₂.1 c₂.2⟩
    · apply Finset.mem_union_right
      rw [compatible_iff_llaves] at ok
      push_neg at ok
      obtain ⟨i,hi⟩:=ok
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨old,hi.symm⟩⟩
  rw [cuenta_fisica_es_cardinal]
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left cap _))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.compatible_iff_llaves
#print axioms ArticuloA.Historias.candidatas_menos_cuatro
