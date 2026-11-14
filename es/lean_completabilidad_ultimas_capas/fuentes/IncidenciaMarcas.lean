import HistoriasLegales

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair

abbrev Vertex := Fin 4 × Nat
def vertex {n} (z e : Cell n) (i : Fin 8) : Vertex := (family i,slot z e i)
def filterG {n} (z e : Cell n) := compatible (corners (z,e)).1 (corners (z,e)).2

private theorem cases8 (i : Fin 8) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
private theorem cases4 (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega

/-- Labels include the family: equal numeric coordinates in two families
are still different vertices. G excludes all repeated vertices in the eight slots. -/
theorem vertices_distinct {n} (z e : Cell n) (G : filterG z e) (i j : Fin 8)
    (eq : vertex z e i = vertex z e j) : i=j := by
  obtain ⟨row,col,d,a⟩ := G
  change z.1 ≠ e.1 at row
  change e.2 ≠ z.2 at col
  have r : z.1.val ≠ e.1.val := fun h => row (Fin.ext h)
  have c : e.2.val ≠ z.2.val := fun h => col (Fin.ext h)
  simp only [corners] at d a
  rcases cases8 i with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases cases8 j with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | rfl | (simp [vertex,family,slot,key,dest,side,lines] at eq <;> omega)

theorem newborn_away {n} (z e : Cell n) (G : filterG z e) (j : Fin 4) :
    key z e j ≠ lines e (side j) := by
  intro h
  rcases cases4 j with rfl|rfl|rfl|rfl
  · have eq := vertices_distinct z e G 4 2 (Prod.ext rfl h); omega
  · have eq := vertices_distinct z e G 5 3 (Prod.ext rfl h); omega
  · have eq := vertices_distinct z e G 6 2 (Prod.ext rfl h); omega
  · have eq := vertices_distinct z e G 7 3 (Prod.ext rfl h); omega

/-- Two specified different families have codegree at most one among real edges. -/
theorem real_codegree {n} (e f : Cell n) (i j : Fin 4) (ne : i ≠ j)
    (a : lines e i = lines f i) (b : lines e j = lines f j) : e=f := by
  rcases cases4 i with rfl|rfl|rfl|rfl <;> rcases cases4 j with rfl|rfl|rfl|rfl <;>
    first | exact (ne rfl).elim | (simp [lines] at a b; apply Prod.ext <;> apply Fin.ext <;> omega)

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.vertices_distinct
#print axioms ArticuloA.Trayectoria.E2.real_codegree
