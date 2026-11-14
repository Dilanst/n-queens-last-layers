import DerivaMediaDelPatronReal
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair
noncomputable section
open Classical

private theorem misma_etiqueta {n} (e f : Cell n) (i j : Fin 4) :
    lineLabel e i=lineLabel f j ↔ i=j ∧ lines e j=lines f j := by
  constructor
  · intro h; obtain rfl : i=j := congrArg Prod.fst h
    exact ⟨rfl,congrArg Prod.snd h⟩
  · rintro ⟨rfl,h⟩; exact Prod.ext rfl h

private theorem pertenece_a_fuente {n} (e f : Cell n) (i : Fin 4) :
    (∃ j,lineLabel e i=lineLabel f j) ↔ lines e i=lines f i := by
  simp [misma_etiqueta]

theorem impactos_sobre_las_fuentes {n} (e f : Cell n) (ok : compatible e f) (i : Fin 4)
    (o v j l : Bool) (a : Choice n) :
    (golpeDelPar e f o v j l a (lineLabel e i) ↔ consumeVertex a i (lines e i) ∧ o=false) ∧
    (golpeDelPar e f o v j l a (lineLabel f i) ↔ consumeVertex a i (lines f i) ∧ v=false) := by
  have sep:=(separadas e f).mp ok i
  have two:=dos_destinos e f ok 2 (by decide)
  have three:=dos_destinos e f ok 3 (by decide)
  simp only [golpeDelPar,pertenece_a_fuente]
  simp only [misma_etiqueta,sep,Ne.symm sep,
    Ne.symm two.1,Ne.symm two.2,Ne.symm three.1,Ne.symm three.2,
    and_false,false_and,and_true,or_false,false_or]
  exact ⟨Iff.rfl,Iff.rfl⟩

theorem impactos_sobre_los_destinos {n} (e f : Cell n) (ok : compatible e f)
    (o v j l : Bool) (a : Choice n) :
    (golpeDelPar e f o v j l a (lineLabel (corners (e,f)).2 2) ↔ borraMarca e f 2 j a) ∧
    (golpeDelPar e f o v j l a (lineLabel (corners (e,f)).2 3) ↔ borraMarca e f 3 l a) := by
  have two:=dos_destinos e f ok 2 (by decide)
  have three:=dos_destinos e f ok 3 (by decide)
  have diff : (2:Fin 4)≠3 := by decide
  simp [golpeDelPar,pertenece_a_fuente,misma_etiqueta,two.1,two.2,three.1,three.2,diff,
    Ne.symm diff,borraMarca,lineLabel]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.impactos_sobre_las_fuentes
#print axioms ArticuloA.Historias.impactos_sobre_los_destinos
