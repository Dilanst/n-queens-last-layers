import ProductoDelEmparejamiento
import UnHueco
namespace ArticuloA.Trayectoria.E2
open ArticuloA Corte ProfileKernel

private theorem separar {α β} (xs : List α) (f : α → β) (nd : (xs.map f).Nodup)
    {a b} (ha : a ∈ xs) (hb : b ∈ xs) (same : f a = f b) : a=b := by
  induction xs with
  | nil => contradiction
  | cons z xs ih =>
    obtain ⟨no,tail⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with az|tailA
    · rcases List.mem_cons.mp hb with bz|tailB
      · exact az.trans bz.symm
      · exact False.elim (no (List.mem_map.mpr ⟨_,tailB,same.symm.trans (congrArg f az)⟩))
    · rcases List.mem_cons.mp hb with bz|tailB
      · exact False.elim (no (List.mem_map.mpr ⟨_,tailA,same.trans (congrArg f bz)⟩))
      · exact ih tail tailA tailB

theorem sin_virtual_fisica {n} (p : Placement n) (legal : Legal p) (full : pieces p = n)
    (L : List (Pieza n)) (real : ∀ e ∈ queens p, Pieza.real e ∈ L)
    (cover : ∀ i, (L.map (fun j => edgeOf j i)).Perm (List.range (2*n-1))) :
    ∀ g, Pieza.virtual g ∈ L → n ≤ g 0 ∧ n ≤ g 1 := by
  have all (f : Cell n → Fin n) (nd : ((queens p).map f).Nodup) (j : Fin n) :
      ∃ e ∈ queens p, f e = j := by
    obtain ⟨free,_,len,hfree⟩ := freeIndices _ nd
    simp only [List.length_map,queenLength,full,Nat.sub_self] at len
    have empty := List.length_eq_zero_iff.mp len
    have use : j ∈ (queens p).map f := by
      apply Classical.byContradiction
      intro absent
      have := (hfree j).2 absent
      simp [empty] at this
    exact List.mem_map.mp use
  intro g hg
  have unique (i : Fin 4) (e : Cell n) (he : e ∈ queens p) (eq : lines e i = g i) : False := by
    have same := separar L (fun j => edgeOf j i) ((cover i).symm.nodup List.nodup_range)
      (real e he) hg eq
    cases same
  constructor
  · apply Nat.le_of_not_lt; intro h
    obtain ⟨e,he,eq⟩ := all _ (distinctRows legal) ⟨g 0,h⟩
    exact unique 0 e he (congrArg Fin.val eq)
  · apply Nat.le_of_not_lt; intro h
    obtain ⟨e,he,eq⟩ := all _ (distinctColumns legal) ⟨g 1,h⟩
    exact unique 1 e he (congrArg Fin.val eq)

theorem producto_de_la_solucion {α n} (s : ProfileScale α) (r c d a : Nat → α)
    (p : Placement n) (legal : Legal p) (full : pieces p = n)
    (L : List (Pieza n)) (real : ∀ e ∈ queens p, Pieza.real e ∈ L)
    (cover : ∀ i, (L.map (fun j => edgeOf j i)).Perm (List.range (2*n-1))) :
    producto s (pesoPieza s (fullColors s n r c d a)) L =
      s.four (fun i => producto s (efectivo s n r c d a i) (List.range (2*n-1))) :=
  producto_lleno s r c d a L cover (sin_virtual_fisica p legal full L real cover)
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.producto_de_la_solucion
