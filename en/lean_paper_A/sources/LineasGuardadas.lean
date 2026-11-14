import SeguimientoPerfil
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA

private theorem four_cases (j : Fin 4) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega

theorem on_board {n} (e : Cell n) (j : Fin 4) : lines e j < 2*n-1 := by
  have a := e.1.isLt; have b := e.2.isLt
  rcases four_cases j with rfl|rfl|rfl|rfl <;> simp [lines] <;> omega

theorem own_vertex {n} (z e : Cell n) (j : Fin 4) :
    vertex z e (ix (.inl j)) = (j,lines e j) := by
  rcases four_cases j with rfl|rfl|rfl|rfl <;> rfl

theorem target_vertex {n} (z e : Cell n) (j : Fin 4) :
    vertex z e (ix (.inr j)) = (side j,key z e j) := by
  rcases four_cases j with rfl|rfl|rfl|rfl <;> rfl

theorem guarded_active {n} (occ : Bool) (x : State n) (z e : Cell n) (m : Marks) (i : Both)
    (listed : i ∈ lossKeys occ) (live : guardP occ x z e m i) :
    let v := vertex z e (ix i)
    v.2 < 2*n-1 ∧ x.active v.1 v.2 = true := by
  dsimp only
  cases i with
  | inl j =>
    rw [own_vertex]; refine ⟨on_board e j,?_⟩
    cases occ with
    | true => simp [lossKeys] at listed
    | false =>
      have active : available x (lines e) = true := live.2.1
      exact List.all_eq_true.mp active j (by simp [List.finRange,List.mem_ofFn] <;> omega)
  | inr j =>
    rw [target_vertex]; refine ⟨on_board (dest z e j) (side j),?_⟩
    have marked' : marked x z e (promote m j) := by cases occ <;> exact live.2.2
    simpa [promote] using marked' j

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.guarded_active
