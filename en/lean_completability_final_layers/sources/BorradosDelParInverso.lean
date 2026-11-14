import GeometriaDeLaInversa
import RestoPares
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

def lineLabel {n} (e : Cell n) (j : Fin 4) : Vertex := (j,lines e j)
def diez {n} (e f : Cell n) : List Vertex :=
  [lineLabel e 0,lineLabel e 1,lineLabel e 2,lineLabel e 3,
   lineLabel f 0,lineLabel f 1,lineLabel f 2,lineLabel f 3,
   lineLabel (corners (e,f)).2 2,lineLabel (corners (e,f)).2 3]

theorem diez_distintas {n} (e f : Cell n) (ok : compatible e f) : (diez e f).Nodup := by
  have s := (separadas e f).mp ok
  have r := s 0; have c := s 1; have d := s 2; have a := s 3
  have h₂ := dos_destinos e f ok 2 (by decide)
  have h₃ := dos_destinos e f ok 3 (by decide)
  simp only [diez,lineLabel,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    Prod.mk.injEq,not_or] 
  simp_all +decide
  exact ⟨fun H => h₂.1 H.symm,fun H => h₃.1 H.symm,fun H => h₂.2 H.symm,fun H => h₃.2 H.symm⟩

private theorem distintos {α} (l : List α) (h : l.Nodup) (ij : α × α)
    (hp : ij ∈ pairs l) : ij.1 ≠ ij.2 := by
  induction l with
  | nil => simp [pairs] at hp
  | cons i l ih =>
    rcases List.mem_append.mp hp with H|H
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp H
      intro eq; change i=j at eq
      exact (List.nodup_cons.mp h).1 (eq.symm ▸ hj)
    · exact ih (List.nodup_cons.mp h).2 H

/-- Handles an arbitrary subset of death marks in a pattern, including
virtual steps. The excess over a single hit is bounded by 45 times
the true real-and-virtual two-line budget on the given transition. -/
theorem borrados_dobles {n α} {s : ProfileScale α} {x : State n} {u : ColorWeights α}
    {inv : α → α} (B : AtomBounds s x u inv) (e f : Cell n) (ok : compatible e f)
    (hit : Choice n → Vertex → Prop)
    (cover : ∀ a i, hit a i → consumeVertex a i.1 i.2) :
    s.le (meanN s (choices s x u inv) (fun a => deathsOn (diez e f) (hit a)-1))
      (s.times 45 B.pairCap) := by
  have cnt : (pairs (diez e f)).length = 45 := rfl
  rw [←cnt]
  apply exchange_bound
  intro ij hij
  exact pair_mass s x u inv B.realNormal B.virtualNormal B.realCap B.virtualCap B.capR B.capV
    ij.1 ij.2 (distintos _ (diez_distintas _ _ ok) _ hij) _
    (fun a h => ⟨cover a ij.1 h.1,cover a ij.2 h.2⟩)
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.borrados_dobles
