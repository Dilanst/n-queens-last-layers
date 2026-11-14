import DescomposicionInversa
namespace ArticuloA.Trayectoria.E2
open ArticuloA Repair

/-- A distance budget counted in units of the uniform bound on one weight. -/
structure WeightBudget {α : Type} (s : SumLaw α) where
  near : Nat → α → α → Prop
  reflex : ∀ a, near 0 a a
  symm : ∀ {t a b}, near t a b → near t b a
  chain : ∀ {i j a b c}, near i a b → near j b c → near (i+j) a c
  plus : ∀ {i j a b c d}, near i a b → near j c d → near (i+j) (s.plus a c) (s.plus b d)
  weaken : ∀ {i j a b}, i ≤ j → near i a b → near j a b

private theorem perm_over {α β} (s : SumLaw α) (w : β → α) {l m : List β}
    (h : l.Perm m) : s.over l w = s.over m w := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (s.plus (w a)) ih
  | swap a b l =>
    change s.plus _ (s.plus _ _) = s.plus _ (s.plus _ _)
    rw [←s.assoc, s.comm (w b) (w a), s.assoc]
  | trans _ _ ih jh => exact ih.trans jh

private theorem over_append {α β} (s : SumLaw α) (w : β → α) (l m : List β) :
    s.over (l++m) w = s.plus (s.over l w) (s.over m w) := by
  induction l with
  | nil => exact (s.zero_add _).symm
  | cons a l ih =>
    change s.plus _ (s.over (l++m) w) = s.plus (s.plus _ _) _
    rw [ih,s.assoc]; rfl

private theorem list_bound {α β} (s : SumLaw α) (b : WeightBudget s) (w : β → α)
    (cap : ∀ x, b.near 1 (w x) s.zero) (l : List β) :
    b.near l.length (s.over l w) s.zero := by
  induction l with
  | nil => exact b.reflex _
  | cons a l ih =>
    have H := b.plus (cap a) ih
    rw [s.zero_add,Nat.add_comm 1] at H
    exact H

noncomputable def totalInverso {α n} (s : SumLaw α) (w : Cell n → α) (p : Placement n) :=
  s.over (invMarks p) (fun m => w (corners m).1)

theorem salto_ponderado {α n} (s : SumLaw α) (b : WeightBudget s) (w : Cell n → α)
    (cap : ∀ z, b.near 1 (w z) s.zero) (p : Placement n) (ok : Legal p)
    (g : Cell n) (fresh : g ∉ queens p) :
    b.near (4*n) (totalInverso s w p) (totalInverso s w (toggle g p)) := by
  let v := fun m : Mark n => w (corners m).1
  obtain ⟨same,lost,born,h₁,h₂,lo,hi⟩ := cambio_de_lista p ok g fresh
  unfold totalInverso
  rw [perm_over s v h₁,perm_over s v h₂,over_append,over_append]
  have H := b.chain (list_bound s b v (fun _ => cap _) lost)
    (b.symm (list_bound s b v (fun _ => cap _) born))
  apply b.weaken (i := 0+(lost.length+born.length)) (by omega)
  exact b.plus (b.reflex _) H

/-- A virtual step leaves the physical board fixed. Real steps need only
freshness and legality before the insertion. -/
inductive TerminalPath {n} : Placement n → Nat → Placement n → Prop where
  | start (p) : TerminalPath p 0 p
  | real {p q t} (h : TerminalPath p t q) (g : Cell n) (ok : Legal q)
      (fresh : g ∉ queens q) : TerminalPath p (t+1) (toggle g q)
  | virtual {p q t} (h : TerminalPath p t q) : TerminalPath p t q

theorem corte_inverso_ponderado {α n} (s : SumLaw α) (b : WeightBudget s)
    (w : Cell n → α) (cap : ∀ z, b.near 1 (w z) s.zero) {p q t}
    (path : TerminalPath (n:=n) p t q) :
    b.near (4*n*t) (totalInverso s w p) (totalInverso s w q) := by
  induction path with
  | start => simpa using b.reflex _
  | real _ g ok fresh ih =>
    simpa only [Nat.mul_succ] using b.chain ih (salto_ponderado s b w cap _ ok g fresh)
  | virtual _ ih => exact ih
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.salto_ponderado
#print axioms ArticuloA.Trayectoria.E2.corte_inverso_ponderado
