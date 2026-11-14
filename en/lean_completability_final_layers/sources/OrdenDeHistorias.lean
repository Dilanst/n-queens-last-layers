import PiezasDeUnaHistoria
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical

private theorem solo_casillas {n : ℕ} {xs : List (Cell n)} (p : Mask xs) :
    ∀ e ∈ queens p, e ∈ xs := by
  induction p with
  | empty => simp [queens]
  | skip b ih => intro e he; exact List.mem_cons_of_mem _ (ih e he)
  | take b ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl|ht
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih e ht)

private theorem mascara_unica {n : ℕ} {xs : List (Cell n)} (p b : Mask xs)
    (nd : xs.Nodup) (eq : ∀ e, e ∈ queens p ↔ e ∈ queens b) : p=b := by
  induction p with
  | empty => cases b; rfl
  | @skip x xs p ih =>
    obtain ⟨no,hd⟩ := List.nodup_cons.mp nd
    cases b with
    | skip t => exact congrArg Mask.skip (ih t hd eq)
    | take t =>
      exact False.elim (no (solo_casillas p x ((eq x).mpr List.mem_cons_self)))
  | @take x xs p ih =>
    obtain ⟨no,hd⟩ := List.nodup_cons.mp nd
    cases b with
    | skip t => exact False.elim (no (solo_casillas t x ((eq x).mp List.mem_cons_self)))
    | take t =>
      apply congrArg Mask.take
      apply ih t hd
      intro e
      by_cases same : e=x
      · subst e
        exact iff_of_false (fun h => no (solo_casillas p _ h)) (fun h => no (solo_casillas t _ h))
      · simpa [queens,same] using eq e

def secuencia {n q : ℕ} (H : Historia n q) (t : Indice n) : Pieza n :=
  pieza H.1 H.2.1 (H.2.2 t)

theorem reales_de_la_secuencia {n q : ℕ} (H : Historia n q) (e : Cell n) :
    (∃ t, secuencia H t = .real e) ↔ e ∈ queens H.1.val := by
  constructor
  · rintro ⟨t,eq⟩; exact memoria _ _ _ e eq
  · intro he
    obtain ⟨t,eq⟩ := H.2.2.surjective (⟨lines e 0,rango e 0⟩ : Indice n)
    exact ⟨t,by rw [secuencia,eq]; exact encuentra _ _ e he⟩

theorem secuencia_inyectiva {n q : ℕ} : Function.Injective (@secuencia n q) := by
  rintro ⟨P,C,O⟩ ⟨Q,D,V⟩ eq
  have sameP : P=Q := by
    apply Subtype.ext
    apply mascara_unica _ _ (board_unique n)
    intro e
    exact (reales_de_la_secuencia ⟨P,C,O⟩ e).symm.trans (by rw [eq]; exact reales_de_la_secuencia ⟨Q,D,V⟩ e)
  subst Q
  have sameO : O=V := by
    apply Equiv.ext; intro t
    apply Fin.ext
    exact (fila_pieza P C (O t)).symm.trans
      ((congrArg (fun a => edgeOf a 0) (congrFun eq t)).trans (fila_pieza P D (V t)))
  subst V
  have sameC : C=D := by
    apply decodificar
    intro r
    let j : Indice n := ⟨r.val,Finset.mem_range.mp (Finset.mem_sdiff.mp r.property).1⟩
    have hj : ¬hayReina P j := by
      rintro ⟨e,he,eq'⟩
      have mem := en_ocupados P e he 0
      rw [eq'] at mem
      exact (Finset.mem_sdiff.mp r.property).2 mem
    have same := congrFun eq (O.symm j)
    change pieza P C (O (O.symm j))=pieza P D (O (O.symm j)) at same
    simp only [Equiv.apply_symm_apply,pieza,dif_neg hj] at same
    exact Pieza.virtual.inj same
  subst D
  rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.secuencia_inyectiva
#print axioms ArticuloA.Historias.reales_de_la_secuencia
