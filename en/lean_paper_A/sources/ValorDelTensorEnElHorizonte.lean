import SaltoYErrorEnElRelojDeE2
import CrucesDeLaConfiguracion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Limites

def inversasDelTablero {n} (P : Placement n) (w : Cell n→ℝ) :=
  ∑ u∈paresCompatibles n,w (corners u).1*estadoEscalar
    (u.1∈queens P ∧ u.2∈queens P ∧ freeDiagonals P (corners u).2)

theorem dos_vacancias_fisicas {n} (P : Placement n) (y : Cell n) :
    (vacant P 2 (lines y 2) ∧ vacant P 3 (lines y 3)) ↔ freeDiagonals P y := by
  have same (x : Cell n) : lines x 2≠lines y 2 ↔ x.1.val+y.2.val≠y.1.val+x.2.val := by
    change x.1.val+(n-1-x.2.val)≠y.1.val+(n-1-y.2.val) ↔ _
    have hx:=x.2.isLt; have hy:=y.2.isLt; omega
  constructor
  · rintro ⟨d,a⟩ x hx; exact ⟨(same x).mp (d x hx),a x hx⟩
  · intro h; exact ⟨fun x hx => (same x).mpr (h x hx).1,fun x hx => (h x hx).2⟩

theorem horizonte_es_conteo_fisico {n} (h T : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (X : State n) :
    totalPonderado X (terminoInverso h p w (horizonteInverso n T T) (fraccionAntes n T))=
      inversasDelTablero X.physical w := by
  unfold totalPonderado inversasDelTablero
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  have onlyTerm : ∑ t : CuatroMarcas,terminoInverso h p w (horizonteInverso n T T) (fraccionAntes n T) t u*
       marcaDelPar X t u =w (corners u).1*marcaDelPar X (true,true,false,false) u := by
    change (∑ t : Bool × Bool × Bool × Bool,_)=_
    simp [Fintype.sum_prod_type,Fintype.sum_bool,terminoInverso,horizonteInverso,coefDelPerfil,coefInverso,monoCuatro]
  rw [onlyTerm]
  simp only [marcaDelPar,patronInverso,estadoFuente,estadoMarca,if_true,Bool.false_eq_true,if_false,dos_vacancias_fisicas]

theorem conteo_en_el_nivel_inverso {n q} (P : Placement n) (w : Cell n→ℝ) (size : pieces P=q+1) (leg : Legal P) :
    sumReal.marks (diagonalWeight sumReal q w P)=inversasDelTablero P w := by
  rw [suma_real_de_marcas,←Fintype.sum_prod_type]
  unfold inversasDelTablero paresCompatibles
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  let good:=u.1∈queens P ∧ u.2∈queens P ∧ freeDiagonals P (corners u).2
  by_cases g:good
  · have h := g
    change _ ∧ _ ∧ _ at h
    by_cases ne:u.1=u.2
    · have off : ¬compatible u.1 u.2 := fun ok => ok.1 (congrArg Prod.fst ne)
      rw [if_neg off]
      simp [diagonalWeight,ne,sumReal]
    · have compat:=legal_pair leg h.1 h.2.1 ne
      simp [diagonalWeight,leg,size,ne,compat,h.1,h.2.1,h.2.2,estadoEscalar,indicator]
  · have off : ¬(u.1≠u.2 ∧ u.1∈queens P ∧ u.2∈queens P ∧ freeDiagonals P (corners u).2) :=
      fun t => g t.2
    simp [diagonalWeight,leg,size,off,estadoEscalar,indicator,good] at g ⊢
    aesop

theorem horizonte_en_la_normalizacion_del_articulo {n h T} (hProc : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ)
    (X : State n) (leg : Legal X.physical) (size : pieces X.physical=n-h+1) :
    totalPonderado X (terminoInverso hProc p w (horizonteInverso n T T) (fraccionAntes n T))/(n:ℝ)^2=
      Iobs n h w X.physical := by
  rw [horizonte_es_conteo_fisico,←conteo_en_el_nivel_inverso X.physical w size leg]
  rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_vacancias_fisicas
#print axioms ArticuloA.Historias.horizonte_es_conteo_fisico
#print axioms ArticuloA.Historias.conteo_en_el_nivel_inverso
#print axioms ArticuloA.Historias.horizonte_en_la_normalizacion_del_articulo
