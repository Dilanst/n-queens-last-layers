import PerdidaDeNuevePorIntercambio
import MultiplicidadPorLasMarcasDelIntercambio
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical

theorem cuenta_fisica_es_cardinal {n} (p : Placement n) (z : Cell n) :
    physicalCount p z=((board n).toFinset.filter (Candidate p z)).card := by
  classical
  have aux (xs : List (Cell n)) (nd : xs.Nodup) :
      tally xs (Candidate p z)=(xs.toFinset.filter (Candidate p z)).card := by
    induction xs with
    | nil => simp [tally,counting,SumLaw.over]
    | cons c xs ih =>
      obtain ⟨nc,nd⟩:=List.nodup_cons.mp nd
      change indicator (Candidate p z c)+tally xs (Candidate p z)=_
      by_cases hc : Candidate p z c
      · simp [ih nd,indicator,hc,Finset.filter_insert,nc,Nat.add_comm]
      · simp [ih nd,indicator,hc,Finset.filter_insert,nc]
  exact aux _ (board_unique n)

theorem existe_cruce_vacio {n} {p : Placement n} (hp : Legal p) (size : pieces p<n) :
    ∃ z : Cell n,emptyCross p z := by
  have missing (f : Cell n→Fin n) (nd : ((queens p).map f).Nodup) :
      ∃ i : Fin n,i∉(queens p).map f := by
    obtain ⟨xs,_,len,eq⟩:=freeIndices _ nd
    rw [List.length_map,queenLength] at len
    cases xs with
    | nil => simp at len; omega
    | cons i xs => exact ⟨i,(eq i).mp (by simp)⟩
  obtain ⟨r,hr⟩:=missing Prod.fst (distinctRows hp)
  obtain ⟨c,hc⟩:=missing Prod.snd (distinctColumns hp)
  refine ⟨(r,c),fun e he=>⟨fun h=>hr (List.mem_map.mpr ⟨e,he,h⟩),
    fun h=>hc (List.mem_map.mpr ⟨e,he,h⟩)⟩⟩

theorem completar_si_hay_nueve_por_hueco {n m : ℕ} (p : Placement n) (hp : Legal p)
    (size : pieces p+m=n) (roots : ∀ z : Cell n,9*m≤physicalCount p z+8) :
    ∃ ms : List (Mark n),ms.length=m ∧ aplicarMarcas ms p∈nivel n n := by
  induction m generalizing p with
  | zero =>
    exact ⟨[],rfl,Finset.mem_filter.mpr ⟨todas _,hp,by simpa using size⟩⟩
  | succ m ih =>
    obtain ⟨z,hz⟩:=existe_cruce_vacio hp (by omega)
    have pos : 0<physicalCount p z:=by have h:=roots z; omega
    rw [cuenta_fisica_es_cardinal] at pos
    obtain ⟨e,he⟩:=Finset.card_pos.mp pos
    have op := (direct_iff_candidate p z e hp hz).mpr (Finset.mem_filter.mp he).2
    let tag : Mark n:=(z,e)
    have hi:=forward_valid op
    have next : ∀ a,9*m≤physicalCount (forward tag p) a+8:=by
      intro a
      have h:=roots a
      have loss:=intercambio_pierde_a_lo_sumo_nueve op a
      change physicalCount p a≤physicalCount (forward tag p) a+9 at loss
      omega
    obtain ⟨ms,len,hms⟩:=ih (forward tag p) hi.2.1 (by rw [hi.1]; omega) next
    exact ⟨tag::ms,by simp [len],hms⟩

theorem contar_salidas_con_absorbedores {n m : ℕ} (buenos : Finset (Placement n))
    (conditions : ∀ p∈buenos,Legal p ∧ pieces p+m=n ∧ ∀ z,9*m≤physicalCount p z+8) :
    buenos.card≤count n n*n^(4*m) := by
  apply cardinal_de_los_parciales_completables
  intro p hp
  obtain ⟨ok,size,roots⟩:=conditions p hp
  obtain ⟨ms,len,endp⟩:=completar_si_hay_nueve_por_hueco p ok size roots
  subst m
  exact ⟨ms.get,by simpa using endp⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuenta_fisica_es_cardinal
#print axioms ArticuloA.Historias.existe_cruce_vacio
#print axioms ArticuloA.Historias.completar_si_hay_nueve_por_hueco
#print axioms ArticuloA.Historias.contar_salidas_con_absorbedores
