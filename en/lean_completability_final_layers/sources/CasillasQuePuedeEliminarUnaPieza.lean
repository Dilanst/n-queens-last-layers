import IncidenciaDeCuatroLineasEnUnPaso
namespace ArticuloA.Historias
open Repair
open scoped BigOperators
noncomputable section
open Classical

def fibraFisicaG {n} (i : Fin 4) (z : Cell n) : Finset (Cell n) :=
  Finset.univ.filter (fun e=>llaveDeLinea i e=llaveDeLinea i z)

theorem longitud_de_la_fibra {n} (i : Fin 4) (z : Cell n) : (fibraFisicaG i z).card≤n := by
  let j : Fin 4:=if i=0 then 1 else 0
  let key : Cell n→Fin n:=fun e=>if i=0 then e.2 else e.1
  have distinct : i≠j:=by by_cases h : i=0 <;> simp [j,h]
  have embed : (fibraFisicaG i z:Set (Cell n)).InjOn key:=by
    intro e he b hb eq
    have first:=(Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hb).2.symm
    apply dos_familias_determinan_la_casilla distinct first
    by_cases h : i=0 <;> simp [key,j,h,llaveDeLinea] at eq ⊢ <;> exact congrArg Fin.val eq
  simpa using (Finset.card_le_card_of_injOn (t:=Finset.univ) key (fun _ _=>Finset.mem_univ _) embed)

def atacadasPor {n} (b : Cell n) : Finset (Cell n) := Finset.univ.filter (fun e=>¬compatible e b)

theorem a_lo_sumo_cuatro_n {n} (b : Cell n) : (atacadasPor b).card≤4*n := by
  have cover : atacadasPor b ⊆ Finset.univ.biUnion (fun i=>fibraFisicaG i b):=by
    intro e he
    have hit:= (Finset.mem_filter.mp he).2
    rw [compatible_iff_llaves] at hit
    push_neg at hit
    obtain ⟨i,eq⟩:=hit
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans ((Finset.sum_le_sum
    (fun i (_ : i∈(Finset.univ : Finset (Fin 4)))=>longitud_de_la_fibra i b)).trans (by simp)))

theorem a_lo_sumo_tres_de_una_linea {n} (i : Fin 4) (z b : Cell n)
    (off : llaveDeLinea i b≠llaveDeLinea i z) : ((fibraFisicaG i z)∩atacadasPor b).card≤3 := by
  let s:=(Finset.univ : Finset (Fin 4)).erase i
  let inter (j : Fin 4):=fibraFisicaG i z∩fibraFisicaG j b
  have cover : fibraFisicaG i z∩atacadasPor b⊆s.biUnion inter:=by
    intro e he
    obtain ⟨root,bad⟩:=Finset.mem_inter.mp he
    have a:=(Finset.mem_filter.mp root).2
    have hit:=(Finset.mem_filter.mp bad).2
    rw [compatible_iff_llaves] at hit
    push_neg at hit
    obtain ⟨j,eq⟩:=hit
    have ne : j≠i:=by rintro rfl; exact off (eq.symm.trans a)
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩,
      Finset.mem_inter.mpr ⟨root,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩⟩
  have small (j) (hj : j∈s) : (inter j).card≤1:=by
    apply Finset.card_le_one.mpr
    intro e he f hf
    obtain ⟨ei,ej⟩:=Finset.mem_inter.mp he
    obtain ⟨fi,fj⟩:=Finset.mem_inter.mp hf
    exact dos_familias_determinan_la_casilla (Finset.mem_erase.mp hj).1
      ((Finset.mem_filter.mp ej).2.trans (Finset.mem_filter.mp fj).2.symm)
      ((Finset.mem_filter.mp ei).2.trans (Finset.mem_filter.mp fi).2.symm)
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans ((Finset.sum_le_sum small).trans
    (by simp [s,Finset.card_erase_of_mem])))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.a_lo_sumo_cuatro_n
#print axioms ArticuloA.Historias.a_lo_sumo_tres_de_una_linea
