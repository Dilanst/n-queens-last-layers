import MasaDeNacimientoDelParInverso
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair
noncomputable section

def evitaFuente {n} (a : Choice n) (e : Cell n) (o : Bool) : Prop :=
  o = true ∨ ∀ i, ¬consumeVertex a i (lines e i)

def borraMarca {n} (e f : Cell n) (i : Fin 4) (j : Bool) (a : Choice n) : Prop :=
  consumeVertex a i (lines (corners (e,f)).2 i) ∧ (j=true ∨ isReal a)

theorem fuente_persistente {n} (X : State n) (e : Cell n) (o : Bool) (a : Choice n)
    (fresh : admissible X a) (other : ¬bornHere e a) :
    estadoFuente (next X a) e o ↔ estadoFuente X e o ∧ evitaFuente a e o := by
  cases o with
  | false => simpa only [estadoFuente,evitaFuente,Bool.false_eq_true,false_or,if_false,eraseOwn] using available_after X a e
  | true =>
    cases a with
    | real c =>
      change e∈queens (toggle c X.physical) ↔ e∈queens X.physical ∧ _
      rw [inserted X.physical c fresh e]
      change ¬e=c at other
      simp [other,evitaFuente]
    | virtual g => simp [estadoFuente,evitaFuente,next]
    | fail => simp [estadoFuente,evitaFuente,next]

theorem destino_persistente {n} (X : State n) (e f : Cell n) (i : Fin 4) (j : Bool)
    (a : Choice n) (fresh : admissible X a) :
    estadoMarca (next X a) e f i j ↔ estadoMarca X e f i j ∧ ¬borraMarca e f i j a := by
  let v:=lines (corners (e,f)).2 i
  cases j with
  | true =>
    cases a <;> simp [estadoMarca,borraMarca,next,consume,consumeVertex,ne_comm]
  | false =>
    cases a with
    | fail => simp [estadoMarca,borraMarca,next,consumeVertex]
    | virtual g => simp [estadoMarca,borraMarca,next,isReal]
    | real c =>
      change vacant (toggle c X.physical) i v ↔ vacant X.physical i v ∧ ¬(lines c i=v ∧ (false=true ∨ True))
      by_cases hit : lines c i=v
      · have no : ¬vacant (toggle c X.physical) i v := fun H => H c ((inserted _ c fresh c).mpr (.inl rfl)) hit
        simp [no,hit]
      · simpa [hit] using vacant_insert X.physical c fresh i v hit

def sobreviveElPar {n} (e f : Cell n) (o v j l : Bool) (a : Choice n) : Prop :=
  evitaFuente a e o ∧ evitaFuente a f v ∧ ¬borraMarca e f 2 j a ∧ ¬borraMarca e f 3 l a

theorem paso_exacto_del_patron {n} (X : State n) (e f : Cell n) (o v j l : Bool)
    (a : Choice n) (ok : compatible e f) (coh : coherent X) (live : allowed X a) :
    patronInverso (next X a) e f o v j l ↔
      (patronInverso X e f o v j l ∧ sobreviveElPar e f o v j l a) ∨
      (o=true ∧ bornHere e a ∧ patronInverso X e f false v j l) ∨
      (v=true ∧ bornHere f a ∧ patronInverso X e f o false j l) := by
  have fresh:=choice_adm coh a live
  by_cases b : bornHere e a
  · cases a with
    | fail => exact b.elim
    | virtual g => exact b.elim
    | real c =>
      change e=c at b
      subst c
      have ne : f≠e := fun eq => ok.1 (congrArg Prod.fst eq.symm)
      have old : e∉queens X.physical := fresh
      have killed : ¬evitaFuente (.real e) e false := by simp [evitaFuente,consumeVertex]
      have off : E2.available (next X (.real e)) (lines e)≠true := by
        intro h
        exact (available_after X (.real e) e).mp h |>.2 0 rfl
      cases o
      · simp [patronInverso,estadoFuente,off,sobreviveElPar,killed,bornHere,ne]
      · simp only [bornHere,ne,and_false,false_and,or_false,eq_self,true_and]
        rw [nace_primera_fuente X e f ok fresh live]
        simp [patronInverso,estadoFuente,old]
  by_cases d : bornHere f a
  · cases a with
    | fail => exact d.elim
    | virtual g => exact d.elim
    | real c =>
      change f=c at d
      subst c
      have old : f∉queens X.physical := fresh
      have killed : ¬evitaFuente (.real f) f false := by simp [evitaFuente,consumeVertex]
      have off : E2.available (next X (.real f)) (lines f)≠true := by
        intro h
        exact (available_after X (.real f) f).mp h |>.2 0 rfl
      cases v
      · simp [patronInverso,estadoFuente,off,sobreviveElPar,killed,b,bornHere] at *
        tauto
      · simp only [b,and_false,false_and,false_or,bornHere,eq_self,true_and]
        rw [nace_segunda_fuente X e f ok fresh live]
        simp [patronInverso,estadoFuente,old]
  · simp only [b,d,false_and,and_false,false_or,or_false]
    unfold patronInverso sobreviveElPar
    rw [fuente_persistente X e o a fresh b,fuente_persistente X f v a fresh d,
      destino_persistente X e f 2 j a fresh,destino_persistente X e f 3 l a fresh]
    tauto

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.paso_exacto_del_patron
