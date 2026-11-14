import Mathlib.Data.Fintype.BigOperators
import LeyUniformeDelTablero
import Mathlib.Data.Finset.Pairwise
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical

def soporteFisico {n xs} (p : @Mask (Cell n) xs) := (queens p).toFinset

theorem reinas_son_sublista {n xs} (p : @Mask (Cell n) xs) : (queens p).Sublist xs := by
  induction p with
  | empty => exact .slnil
  | skip _ ih => exact .cons _ ih
  | take _ ih => exact .cons₂ _ ih

theorem tamano_soporte {n} (p : Placement n) : (soporteFisico p).card=pieces p := by
  exact (List.toFinset_card_of_nodup ((board_unique n).sublist (reinas_son_sublista p))).trans
    (queenLength p)

theorem legal_iff_pares_del_soporte {n} (p : Placement n) :
    Legal p ↔ (soporteFisico p : Set (Cell n)).Pairwise compatible := by
  apply Iff.symm
  exact List.pairwise_iff_coe_toFinset_pairwise
    ((board_unique n).sublist (reinas_son_sublista p))
    (fun _ _ h=>⟨h.1.symm,h.2.1.symm,h.2.2.1.symm,h.2.2.2.symm⟩)

def elegirCasillas {n : ℕ} (S : Finset (Cell n)) : (xs : List (Cell n))→Mask xs
  | [] => .empty
  | c::xs => if c∈S then .take (elegirCasillas S xs) else .skip (elegirCasillas S xs)

theorem mem_elegidas {n : ℕ} (S : Finset (Cell n)) (xs : List (Cell n)) (e : Cell n) :
    e∈queens (elegirCasillas S xs) ↔ e∈S ∧ e∈xs := by
  induction xs with
  | nil => simp [elegirCasillas,queens]
  | cons c xs ih =>
    by_cases ec : e=c
    · subst e; by_cases h : c∈S <;> simp [elegirCasillas,h,queens,ih]
    · by_cases h : c∈S <;> simp [elegirCasillas,h,queens,ih,ec]

theorem soporte_elegido {n : ℕ} (S : Finset (Cell n)) :
    soporteFisico (elegirCasillas S (board n))=S := by
  ext c
  simp [soporteFisico,mem_elegidas,board_complete]

theorem eleccion_recupera_mascara {n xs} (p : @Mask (Cell n) xs)
    (nd : xs.Nodup) (S : Finset (Cell n)) (eq : ∀ e∈xs,e∈S ↔ e∈queens p) :
    elegirCasillas S xs=p := by
  induction p with
  | empty => rfl
  | @skip c xs p ih =>
    obtain ⟨miss,uniq⟩:=List.nodup_cons.mp nd
    have no : c∉S:=fun hc=>miss ((reinas_son_sublista p).subset ((eq c (by simp)).mp hc))
    simp only [elegirCasillas,if_neg no]
    exact congrArg Mask.skip (ih uniq (fun e he=>eq e (by simp [he])))
  | @take c xs p ih =>
    obtain ⟨miss,uniq⟩:=List.nodup_cons.mp nd
    have yes : c∈S:=(eq c (by simp)).mpr (by simp [queens])
    simp only [elegirCasillas,if_pos yes]
    apply congrArg Mask.take
    apply ih uniq
    intro e he
    have ne : e≠c:=fun ec=>miss (ec ▸ he)
    simpa [queens,ne] using eq e (List.mem_cons_of_mem _ he)

def conjuntosLegales (n q : ℕ) : Finset (Finset (Cell n)) :=
  (Finset.univ : Finset (Cell n)).powerset.filter (fun S=>S.card=q ∧ (S:Set (Cell n)).Pairwise compatible)

theorem conteo_de_conjuntos_es_el_del_articulo (n q : ℕ) :
    (conjuntosLegales n q).card=count n q := by
  have eq : ↥(nivel n q) ≃ ↥(conjuntosLegales n q) := {
    toFun := fun p=>⟨soporteFisico p.val,by
      have h:=(Finset.mem_filter.mp p.prop).2
      simpa [conjuntosLegales,tamano_soporte] using And.intro h.2 ((legal_iff_pares_del_soporte _).mp h.1)⟩
    invFun := fun s=>⟨elegirCasillas s.val (board n),by
      have h:=(Finset.mem_filter.mp s.prop).2
      apply Finset.mem_filter.mpr
      refine ⟨todas _,(legal_iff_pares_del_soporte _).mpr ?_,?_⟩
      · simpa [soporte_elegido] using h.2
      · rw [←tamano_soporte,soporte_elegido]
        exact h.1⟩
    left_inv := fun p=>Subtype.ext (eleccion_recupera_mascara _ (board_unique _) _
      (fun e _=>by simp [soporteFisico]))
    right_inv := fun s=>Subtype.ext (soporte_elegido _)}
  simpa only [Fintype.card_coe,cardinal_nivel] using (Fintype.card_congr eq).symm

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tamano_soporte
#print axioms ArticuloA.Historias.legal_iff_pares_del_soporte
#print axioms ArticuloA.Historias.conteo_de_conjuntos_es_el_del_articulo
