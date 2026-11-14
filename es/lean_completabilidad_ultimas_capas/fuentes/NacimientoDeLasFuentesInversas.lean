import BorradosFisicosEnLaReparacionInversa
import TransicionPatron
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair
noncomputable section

def estadoFuente {n} (X : State n) (e : Cell n) (ocupada : Bool) : Prop :=
  if ocupada then e∈queens X.physical else E2.available X (lines e)=true

def estadoMarca {n} (X : State n) (e f : Cell n) (i : Fin 4) (activa : Bool) : Prop :=
  let d:=lines (corners (e,f)).2 i
  if activa then X.active i d=true else vacant X.physical i d

def patronInverso {n} (X : State n) (e f : Cell n) (a b j₂ j₃ : Bool) : Prop :=
  estadoFuente X e a ∧ estadoFuente X f b ∧ estadoMarca X e f 2 j₂ ∧ estadoMarca X e f 3 j₃

private theorem marca_no_cambia {n} (X : State n) (e f g : Cell n) (fresh : g∉queens X.physical)
    (j : Fin 4) (v : Bool) (sep : lines (corners (e,f)).2 j≠lines g j) :
    estadoMarca (next X (.real g)) e f j v ↔ estadoMarca X e f j v := by
  cases v
  · exact vacant_insert _ _ fresh _ _ (Ne.symm sep)
  · simp [estadoMarca,next,consume,sep]

private theorem pareja_conservada {n} (X : State n) (other g : Cell n) (fresh : g∉queens X.physical)
    (ne : other≠g) (sep : ∀ i,lines g i≠lines other i) (v : Bool) :
    estadoFuente (next X (.real g)) other v ↔ estadoFuente X other v := by
  cases v
  · exact (available_after X (.real g) other).trans
      ⟨fun h => h.1,fun h => ⟨h,fun i => sep i⟩⟩
  · change other∈queens (toggle g X.physical) ↔ _
    simpa only [ne,false_or,estadoFuente,if_true] using (ArticuloA.Repair.inserted X.physical g fresh other)

/-- A birth at the first source leaves exactly the predecessor. Both destination marks
may independently use physical vacancy or virtual activation. -/
theorem nace_primera_fuente {n} (X : State n) (e f : Cell n) (ok : compatible e f)
    (fresh : e∉queens X.physical) (live : E2.available X (lines e)=true) (v j₂ j₃ : Bool) :
    patronInverso (next X (.real e)) e f true v j₂ j₃ ↔ patronInverso X e f false v j₂ j₃ := by
  have born : estadoFuente (next X (.real e)) e true :=
    (ArticuloA.Repair.inserted X.physical e fresh e).mpr (.inl rfl)
  have dis := (separadas e f).mp ok
  have ne : f≠e := fun eq => ok.1 (congrArg Prod.fst eq.symm)
  simp only [patronInverso,born,true_and,pareja_conservada X f e fresh ne dis v,
    marca_no_cambia X e f e fresh 2 j₂ (dos_destinos e f ok 2 (by decide)).1,
    marca_no_cambia X e f e fresh 3 j₃ (dos_destinos e f ok 3 (by decide)).1,
    show estadoFuente X e false from live]

theorem nace_segunda_fuente {n} (X : State n) (e f : Cell n) (ok : compatible e f)
    (fresh : f∉queens X.physical) (live : E2.available X (lines f)=true) (v j₂ j₃ : Bool) :
    patronInverso (next X (.real f)) e f v true j₂ j₃ ↔ patronInverso X e f v false j₂ j₃ := by
  have born : estadoFuente (next X (.real f)) f true :=
    (ArticuloA.Repair.inserted X.physical f fresh f).mpr (.inl rfl)
  have dis := (separadas e f).mp ok
  have ne : e≠f := fun eq => ok.1 (congrArg Prod.fst eq)
  simp only [patronInverso,born,true_and,pareja_conservada X e f fresh ne (fun i => (dis i).symm) v,
    marca_no_cambia X e f f fresh 2 j₂ (dos_destinos e f ok 2 (by decide)).2,
    marca_no_cambia X e f f fresh 3 j₃ (dos_destinos e f ok 3 (by decide)).2,
    show estadoFuente X f false from live]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.nace_primera_fuente
#print axioms ArticuloA.Historias.nace_segunda_fuente
