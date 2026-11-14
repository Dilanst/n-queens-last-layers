import DerivadaDelTensorDeMarcas
import CuatroEcuacionesDelRelojFisico
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Inversa

def idealDeLaPareja {n} {X : State n} {col} (A : Region masas X col (·⁻¹)) (t : CuatroMarcas) (u : Mark n) :=
  operadorInverso X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2
    (fun e => (↑(A.birth e/(n:ℝ≥0)^2):ℝ)) (fun v b => (intensidadIdeal A v b:ℝ))

theorem cancelar_velocidad_y_generador {n} {X : State n} {col} (A : Region masas X col (·⁻¹))
    (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (u : Mark n) (y z : ℝ≥0) (d : ℝ)
    (hz : A.z=z) (clock : d=((n:ℝ)*(A.c:ℝ))⁻¹)
    (hp : ∀ e : Cell n,(A.piN e:ℝ)/n=(probDeLaCasilla h p e:ℝ))
    (hl : ∀ v : Vertex,A.p v=probLinea n h p v) :
    ∑ t : CuatroMarcas,(d*velocidadDelPerfil h p w y z t u*marcaDelPar X t u+
      terminoInverso h p w y z t u*idealDeLaPareja A t u)=0 := by
  let π:=fun e : Cell n => (probDeLaCasilla h p e:ℝ)
  let L:=fun i => (probLinea n h p (lineLabel (corners u).2 i):ℝ)
  let θ:=fun e => π e*(y:ℝ)/(z:ℝ)^4
  let η:=fun i => L i*(y:ℝ)/(z:ℝ)
  let v:=fun e => d*π e*(-1/(z:ℝ)^4+4*(y:ℝ)/(z:ℝ)^5)
  let a:=fun i => d*L i*(-1/(z:ℝ)+(y:ℝ)/(z:ℝ)^2)
  let O:=fun e o => estadoEscalar (estadoFuente X e o)
  let V:=fun i b => estadoEscalar (estadoMarca X u.1 u.2 i b)
  have eqns (e : Cell n) (i : Fin 4) := cuatro_ecuaciones_en_region A e (lineLabel (corners u).2 i) y
  have eqS (e : Cell n) : v e+(↑(A.birth e/(n:ℝ≥0)^2):ℝ)-
      4*(↑(A.time⁻¹/(n:ℝ≥0)):ℝ)*θ e=0 := by
    have q:=(eqns e 2).1
    rw [hp,hz] at q
    dsimp only [v,θ,π]; rw [clock]
    convert q using 1
    simp only [NNReal.coe_div, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]
    ring
  have eqD (i : Fin 4) : a i+(intensidadIdeal A (lineLabel (corners u).2 i) false:ℝ)-
      (↑(A.time⁻¹/(n:ℝ≥0)):ℝ)*η i=0 := by
    have q:=(eqns u.1 i).2
    rw [hl,hz] at q
    dsimp only [a,η,L]; rw [clock]
    convert q using 1
    simp only [NNReal.coe_div, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_natCast]
    ring
  have adj:=cancelacion_del_adjunto_fisico A u.1 u.2 (θ u.1) (θ u.2) (η 2) (η 3)
    (v u.1) (v u.2) (a 2) (a 3) (eqS _) (eqS _) (eqD _) (eqD _)
  let D:=derivadaCoef (θ u.1) (θ u.2) (η 2) (η 3) (v u.1) (v u.2) (a 2) (a 3)
  have tensor:=derivada_del_tensor (O u.1) (O u.2) (V 2) (V 3)
    (θ u.1) (θ u.2) (η 2) (η 3) (v u.1) (v u.2) (a 2) (a 3)
  let c:=coefInverso (θ u.1) (θ u.2) (η 2) (η 3)
  have base (t) : coefDelPerfil h p y z u t=c t := by
    simp only [c,coefDelPerfil,θ,η,π,L,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_pow]
  have atime (t) : d*velocidadDelPerfil h p w y z t u=w (corners u).1*D t :=
    pendiente_fisica_del_tensor h p w y z d u t
  have cell (t : CuatroMarcas) : marcaDelPar X t u=monoCuatro (O u.1) (O u.2) (V 2) (V 3) t :=
    estado_del_tensor X u.1 u.2 t
  calc _ = w (corners u).1 * ((∑ t,D t*monoCuatro (O u.1) (O u.2) (V 2) (V 3) t)+
            ∑ t,c t*idealDeLaPareja A t u) := by
          simp only [atime,terminoInverso,base,cell,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum,mul_add]
       _ = 0 := by
          rw [show (∑ t,D t*monoCuatro (O u.1) (O u.2) (V 2) (V 3) t)=_ from tensor]
          rw [show _+∑ t,c t*idealDeLaPareja A t u=0 from adj,mul_zero]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cancelar_velocidad_y_generador
