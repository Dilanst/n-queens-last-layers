import FibrasDeLaCuadraturaEnLaReserva
import EntropiaDeLasHolgurasDeLinea
namespace ArticuloA.Historias
open Repair Perfil Trayectoria Trayectoria.E2 Real
open scoped BigOperators
noncomputable section
open Classical

theorem suma_por_cambio_de_etiquetas {E I J : Type*} [Fintype I] [Fintype J]
    (a : E→I) (b : E→J) (F : I→ℝ) (G : J→ℝ)
    (same : ∀ e z,a e=a z ↔ b e=b z) (on : ∀ e,F (a e)=G (b e))
    (offA : ∀ i,(¬∃ e,a e=i) → F i=0) (offB : ∀ j,(¬∃ e,b e=j) → G j=0) :
    ∑ i,F i=∑ j,G j := by
  let H (i : I) (j : J) := if ∃ e,a e=i ∧ b e=j then F i else 0
  have row (i : I) : ∑ j,H i j=F i := by
    by_cases h : ∃ e,a e=i
    · obtain ⟨e,rfl⟩:=h
      rw [Finset.sum_eq_single_of_mem (b e) (Finset.mem_univ _)]
      · simp [H,show ∃ z,a z=a e ∧ b z=b e from ⟨e,rfl,rfl⟩]
      · intro j _ ne
        have h' : ¬∃ z,a z=a e ∧ b z=j := by
          rintro ⟨z,hz,rfl⟩; exact ne ((same z e).mp hz)
        simp [H,h']
    · rw [offA _ h]; apply Finset.sum_eq_zero
      intro j _
      simp [H,offA _ h]
  have col (j : J) : ∑ i,H i j=G j := by
    by_cases h : ∃ e,b e=j
    · obtain ⟨e,rfl⟩:=h
      rw [Finset.sum_eq_single_of_mem (a e) (Finset.mem_univ _)]
      · simp [H,show ∃ z,a z=a e ∧ b z=b e from ⟨e,rfl,rfl⟩,on]
      · intro i _ ne
        have h' : ¬∃ z,a z=i ∧ b z=b e := by
          rintro ⟨z,rfl,hz⟩; exact ne ((same z e).mpr hz)
        simp [H,h']
    · rw [offB _ h]; apply Finset.sum_eq_zero
      intro i _
      have h' : ¬∃ z,a z=i ∧ b z=j:=fun ⟨z,_,eq⟩=>h ⟨z,eq⟩
      simp [H,h']
  calc
    _ = ∑ i,∑ j,H i j := by simp_rw [row]
    _ = ∑ j,∑ i,H i j := Finset.sum_comm
    _ = _ := by simp_rw [col]

def etiquetaDeCasilla {n} (e : Cell n) : Fin 4→FibraDeB1 n
  | 0 => .inl (false,e.1)
  | 1 => .inl (true,e.2)
  | 2 => .inr (etiquetaD e)
  | 3 => .inr (etiquetaA e)

theorem incidencia_etiquetada {n} (e : Cell n) (i : Fin 4) :
    enLaFibra (etiquetaDeCasilla e i) e ∧ familiaDeReserva (etiquetaDeCasilla e i)=i := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

def lineaDeCuadratura {n} (e : Cell n) (i : Fin 4) : Indice n:=⟨lines e i,rango e i⟩

theorem etiquetas_miden_las_mismas_fibras {n} (e z : Cell n) (i j : Fin 4) :
    etiquetaDeCasilla e i=etiquetaDeCasilla z j ↔
      (i,lineaDeCuadratura e i)=(j,lineaDeCuadratura z j) := by
  by_cases same : i=j
  · subst j
    have ec:=e.2.isLt
    have zc:=z.2.isLt
    fin_cases i <;> simp [etiquetaDeCasilla,etiquetaD,etiquetaA,lineaDeCuadratura,lines,Fin.ext_iff]
    omega
  · constructor
    · intro eq
      have bad:=congrArg familiaDeReserva eq
      rw [(incidencia_etiquetada e i).2,(incidencia_etiquetada z j).2] at bad
      exact (same bad).elim
    · intro eq; exact (same (congrArg Prod.fst eq)).elim
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_por_cambio_de_etiquetas
#print axioms ArticuloA.Historias.etiquetas_miden_las_mismas_fibras
