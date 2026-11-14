import FibrasDeHistorias
import CoberturaDelNivelCero
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
abbrev Indice (n : ℕ) := Fin (2*n-1)
variable {n q : ℕ} (P : Tablero n q)

theorem en_ocupados (e : Cell n) (he : e ∈ queens P.val) (i : Fin 4) :
    lines e i ∈ ocupados P i := List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem rango (e : Cell n) (i : Fin 4) : lines e i < 2*n-1 := by
  have r := e.1.isLt; have c := e.2.isLt
  have cases4 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases4 with rfl|rfl|rfl|rfl <;> simp [lines] <;> omega

theorem dueno_real {e f : Cell n} (he : e∈queens P.val) (hf : f∈queens P.val)
    {i : Fin 4} (eq : lines e i=lines f i) : e=f := by
  by_contra ne
  exact (separadas e f).mp (legal_pair (legal_y_tamano P).1 he hf ne) i eq

theorem en_libres (C : Completion P) (r : libres P 0) (i : Fin 4) : arista C r i ∈ libres P i := by
  have cases4 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases4 with rfl|rfl|rfl|rfl
  · exact r.property
  · exact (C.1 r).property
  · exact (C.2.1 r).property
  · exact (C.2.2 r).property

theorem dueno_virtual (C : Completion P) {r s : libres P 0} (i : Fin 4)
    (eq : arista C r i = arista C s i) : r=s := by
  have cases4 : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases4 with rfl|rfl|rfl|rfl
  · exact Subtype.ext eq
  · exact C.1.injective (Subtype.ext eq)
  · exact C.2.1.injective (Subtype.ext eq)
  · exact C.2.2.injective (Subtype.ext eq)

def hayReina (r : Indice n) := ∃ e ∈ queens P.val, lines e 0=r.val

theorem fila_libre (r : Indice n) (h : ¬hayReina P r) : r.val ∈ libres P 0 :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr r.isLt,fun m => h (List.mem_map.mp (List.mem_toFinset.mp m))⟩

def pieza (C : Completion P) (r : Indice n) : Pieza n :=
  if h : hayReina P r then .real h.choose else .virtual (arista C ⟨r.val,fila_libre P r h⟩)

theorem fila_pieza (C : Completion P) (r : Indice n) : edgeOf (pieza P C r) 0 = r.val := by
  unfold pieza; split
  · rename_i h; exact h.choose_spec.2
  · rfl

theorem encuentra (C : Completion P) (e : Cell n) (he : e ∈ queens P.val) :
    pieza P C ⟨lines e 0,rango e 0⟩ = Pieza.real e := by
  let r : Indice n := ⟨lines e 0,rango e 0⟩
  have ex : hayReina P r := ⟨e,he,rfl⟩
  change pieza P C r = _
  rw [pieza,dif_pos ex]
  exact congrArg Pieza.real (dueno_real P ex.choose_spec.1 he ex.choose_spec.2)

theorem memoria (C : Completion P) (r : Indice n) (e : Cell n) (eq : pieza P C r = .real e) :
    e ∈ queens P.val := by
  unfold pieza at eq
  split at eq
  · rename_i h
    cases eq; exact h.choose_spec.1
  · cases eq

def vertice (C : Completion P) (i : Fin 4) (r : Indice n) : Indice n :=
  ⟨edgeOf (pieza P C r) i,by
    unfold pieza; split
    · exact rango _ _
    · exact Finset.mem_range.mp (Finset.mem_sdiff.mp (en_libres P C _ i)).1⟩

theorem unico (C : Completion P) (i : Fin 4) : Function.Injective (vertice P C i) := by
  intro r s eq
  have E : edgeOf (pieza P C r) i=edgeOf (pieza P C s) i := congrArg Fin.val eq
  by_cases hr : hayReina P r <;> by_cases hs : hayReina P s
  · rw [pieza,dif_pos hr,pieza,dif_pos hs] at E
    have same := dueno_real P hr.choose_spec.1 hs.choose_spec.1 E
    exact Fin.ext (hr.choose_spec.2.symm.trans ((congrArg (fun e => lines e 0) same).trans hs.choose_spec.2))
  · rw [pieza,dif_pos hr,pieza,dif_neg hs] at E
    simp only [edgeOf] at E
    exact False.elim ((Finset.mem_sdiff.mp (en_libres P C _ i)).2 (E ▸ en_ocupados P _ hr.choose_spec.1 i))
  · rw [pieza,dif_neg hr,pieza,dif_pos hs] at E
    simp only [edgeOf] at E
    exact False.elim ((Finset.mem_sdiff.mp (en_libres P C _ i)).2 (E.symm ▸ en_ocupados P _ hs.choose_spec.1 i))
  · rw [pieza,dif_neg hr,pieza,dif_neg hs] at E
    exact Fin.ext (congrArg Subtype.val (dueno_virtual P C i E))

def cobertura (C : Completion P) (i : Fin 4) : Equiv.Perm (Indice n) :=
  Equiv.ofBijective (vertice P C i) ⟨unico P C i,Finite.injective_iff_surjective.mp (unico P C i)⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cobertura
#print axioms ArticuloA.Historias.encuentra
