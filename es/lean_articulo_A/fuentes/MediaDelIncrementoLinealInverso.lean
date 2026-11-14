import MediaDeUnaSumaDeMarcas
import CancelacionDelRelojEnUnaPareja
import DerivaInversaConErrorTotal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
def linealDeUnaJugada {n} (X : State n) (c v : CuatroMarcas→Mark n→ℝ) (a : Choice n) :=
  ∑ j : CuatroMarcas,∑ u∈paresCompatibles n,
    (c j u*(marcaDelPar (next X a) j u-marcaDelPar X j u)+v j u*marcaDelPar X j u)

theorem normalizacion_en_la_region {n} {X : State n} {col} (A : Region masas X col (·⁻¹))
    (run : X.failed=false) :
    total masas (choices masas X col (·⁻¹))=1 := by
  have rem : X.reals+X.virtuals≠0 := by
    intro zero; apply A.running
    change ns masas X.reals+ns masas X.virtuals=0
    rw [ns_real,ns_real,←Nat.cast_add,zero,Nat.cast_zero]
  exact choices_total masas X 0 col (·⁻¹) (fun _ h => inv_mul_cancel₀ h) (by
    intro i j nz; change ns masas i+ns masas j≠0
    rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast nz) run rem

theorem media_lineal_de_la_jugada {n} {X : State n} {col} (A : Region masas X col (·⁻¹))
    (run : X.failed=false) (c v : CuatroMarcas→Mark n→ℝ)
    (cancel : ∀ u∈paresCompatibles n,∑ t : CuatroMarcas,
      (v t u*marcaDelPar X t u+c t u*idealDeLaPareja A t u)=0) :
    media (choices masas X col (·⁻¹)) (linealDeUnaJugada X c v)=
      ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,c t u*errorDeDeriva A t u := by
  let row:=choices masas X col (·⁻¹)
  have norm:=normalizacion_en_la_region A run
  have term (t : CuatroMarcas) (u : Mark n) :
      media row (fun a => c t u*(marcaDelPar (next X a) t u-marcaDelPar X t u)+v t u*marcaDelPar X t u) =
      c t u*errorDeDeriva A t u+(v t u*marcaDelPar X t u+c t u*idealDeLaPareja A t u) := by
    let U:=fun a : Choice n => marcaDelPar (next X a) t u
    let m:=marcaDelPar X t u
    have form (a : Choice n) : c t u*(U a-m)+v t u*m=c t u*U a+(v t u*m-c t u*m) := by ring
    change media row (fun a => c t u*(U a-m)+v t u*m)=_
    simp_rw [form]
    rw [media_con_constante row norm]
    have obs:=media_de_una_marca row (fun a => patronInverso (next X a) u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2)
    change media row U=_ at obs
    rw [obs]
    dsimp only [m,errorDeDeriva,idealDeLaPareja,marcaDelPar,estadoEscalar,row]; ring
  unfold linealDeUnaJugada
  change media row (fun a => ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,_) = _
  rw [media_de_suma_finita]
  simp_rw [media_de_suma_finita,term]
  simp only [Finset.sum_add_distrib]
  have zero : (∑ t : CuatroMarcas,∑ u∈paresCompatibles n,(v t u*marcaDelPar X t u+c t u*idealDeLaPareja A t u))=0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero cancel
  simpa only [Finset.sum_add_distrib] using congrArg (fun z =>
    (∑ t : CuatroMarcas,∑ u∈paresCompatibles n,c t u*errorDeDeriva A t u)+z) zero |>.trans (add_zero _)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_en_la_region
#print axioms ArticuloA.Historias.media_lineal_de_la_jugada
