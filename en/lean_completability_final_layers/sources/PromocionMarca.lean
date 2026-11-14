import FuenteNacimiento
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

def promote (m : Marks) (j : Fin 4) : Marks := fun k => if k=j then true else m k

theorem active_vacant {n} (x : State n) (good : coherent x) (f : Fin 4) (v : Nat)
    (yes : x.active f v = true) : vacant x.physical f v := by
  intro e old eq
  have off := good.2 e old f
  rw [eq,yes] at off; contradiction

theorem promoted {n} (x : State n) (good : coherent x) (z e : Cell n) (m : Marks) (j : Fin 4) :
    marked x z e (promote m j) ↔ marked x z e m ∧ x.active (side j) (key z e j) = true := by
  constructor
  · intro all
    have on : x.active (side j) (key z e j) = true := by simpa [promote] using all j
    refine ⟨?_,on⟩; intro k
    by_cases eq : k=j
    · subst k; cases m j
      · exact active_vacant x good _ _ on
      · exact on
    · simpa [promote,eq] using all k
  · rintro ⟨old,on⟩ k
    by_cases eq : k=j
    · subst k; simpa [promote] using on
    · simpa [promote,eq] using old k

private theorem consume_live {n} (x : State n) (a : Choice n) (ok : allowed x a) (f : Fin 4) (v : Nat)
    (hit : consumeVertex a f v) : x.active f v = true := by
  have mem : f ∈ List.finRange 4 := by simp [List.finRange,List.mem_ofFn] <;> omega
  cases a with
  | fail => exact hit.elim
  | real c => exact hit ▸ (List.all_eq_true.mp ok f mem)
  | virtual g => exact hit ▸ (List.all_eq_true.mp ok f mem)

def pattern {n} (occ : Bool) (x : State n) (z e : Cell n) (m : Marks) :=
  if occ then occupied x z e m else availPattern x z e m

theorem single_vacancy {n} (occ : Bool) (x : State n) (good : coherent x) (z e : Cell n)
    (m : Marks) (j : Fin 4) (vac : m j = false) (a : Choice n) (ok : allowed x a) :
    (pattern occ x z e m ∧ eraseDest z e m a j) ↔
    (pattern occ x z e (promote m j) ∧ consumeVertex a (side j) (key z e j) ∧ isReal a) := by
  by_cases hit : consumeVertex a (side j) (key z e j)
  · have on := consume_live x a ok _ _ hit
    cases occ <;> simp [pattern,occupied,availPattern,eraseDest,vac,hit,promoted x good,on]
  · simp [eraseDest,hit]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.single_vacancy
