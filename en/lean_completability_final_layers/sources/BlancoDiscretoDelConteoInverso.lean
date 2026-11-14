import SaltoYErrorEnElRelojDeE2
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
def blancoInverso {n} (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (y : ℝ≥0) :=
  ∑ u∈paresCompatibles n,w (corners u).1*((probDeLaCasilla h p u.1:ℝ)*y)*
    ((probDeLaCasilla h p u.2:ℝ)*y)*(1-(probLinea n h p (lineLabel (corners u).2 2):ℝ)*y)*
    (1-(probLinea n h p (lineLabel (corners u).2 3):ℝ)*y)

theorem blanco_inverso_al_inicio {n} (hn : 2≤n) (h T : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) :
    totalPonderado (initial n h) (terminoInverso h p w (horizonteInverso n T 0) (fraccionAntes n 0))=
      blancoInverso h p w (horizonteInverso n T 0) := by
  have nz : (↑(2*n-1):ℝ≥0)≠0 := by exact_mod_cast (show 2*n-1≠0 by omega)
  have clock : fraccionAntes n 0=1 := by simp only [fraccionAntes,Nat.sub_zero,div_self nz]
  have empty (xs : List (Cell n)) : queens (emptyMask xs)=[] := by
    induction xs with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold totalPonderado blancoInverso
  rw [Finset.sum_comm,clock]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ t : Bool × Bool × Bool × Bool,_)=_
  simp [Fintype.sum_prod_type,Fintype.sum_bool,terminoInverso,coefDelPerfil,coefInverso,monoCuatro,
    marcaDelPar,estadoEscalar,patronInverso,estadoFuente,estadoMarca,indicator,initial,empty,E2.available,vacant]
  ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.blanco_inverso_al_inicio
