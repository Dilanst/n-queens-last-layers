import PasoTemporaldelPerfilFisico
import DieciseisPatronesEnUnMismoAtomo
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Inversa

def derivadaCoef (θ ξ η μ v w a b : ℝ) (t : CuatroMarcas) :=
  productRule (if t.1 then 1 else θ) (if t.2.1 then 1 else ξ)
    (if t.2.2.1 then -η else 1) (if t.2.2.2 then -μ else 1)
    (if t.1 then 0 else v) (if t.2.1 then 0 else w)
    (if t.2.2.1 then -a else 0) (if t.2.2.2 then -b else 0)

theorem derivada_del_tensor (A B C D : Bool→ℝ) (θ ξ η μ v w a b : ℝ) :
    ∑ t : CuatroMarcas,derivadaCoef θ ξ η μ v w a b t*monoCuatro A B C D t =
      productRule (pairForm (A true) (A false) θ) (pairForm (B true) (B false) ξ)
        (pairForm (C false) (C true) (-η)) (pairForm (D false) (D true) (-μ))
        (v*A false) (w*B false) (-a*C true) (-b*D true) := by
  change (∑ t : Bool × Bool × Bool × Bool,_) = _
  simp [Fintype.sum_prod_type,Fintype.sum_bool,derivadaCoef,monoCuatro,productRule,pairForm]
  ring

theorem estado_del_tensor {n} (X : State n) (e f : Cell n) (t : CuatroMarcas) :
    marcaDelPar X t (e,f) =
      monoCuatro (fun o => estadoEscalar (estadoFuente X e o)) (fun o => estadoEscalar (estadoFuente X f o))
        (fun j => estadoEscalar (estadoMarca X e f 2 j)) (fun j => estadoEscalar (estadoMarca X e f 3 j)) t := by
  have split (P Q : Prop) : estadoEscalar (P ∧ Q)=estadoEscalar P*estadoEscalar Q := by
    by_cases a:P <;> by_cases b:Q <;> simp [a,b,estadoEscalar,indicator]
  simp only [marcaDelPar,patronInverso,monoCuatro,split]
  ring

theorem pendiente_fisica_del_tensor {n} (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ)
    (y z : ℝ≥0) (d : ℝ) (u : Mark n) (t : CuatroMarcas) :
    let π:=fun e : Cell n => (probDeLaCasilla h p e:ℝ)
    let l:=fun i => (probLinea n h p (lineLabel (corners u).2 i):ℝ)
    let θ:=fun e => π e*(y:ℝ)/(z:ℝ)^4
    let η:=fun i => l i*(y:ℝ)/(z:ℝ)
    let v:=fun e => d*π e*(-1/(z:ℝ)^4+4*(y:ℝ)/(z:ℝ)^5)
    let a:=fun i => d*l i*(-1/(z:ℝ)+(y:ℝ)/(z:ℝ)^2)
    d*velocidadDelPerfil h p w y z t u=w (corners u).1*
      derivadaCoef (θ u.1) (θ u.2) (η 2) (η 3) (v u.1) (v u.2) (a 2) (a 3) t := by
  intro π l θ η v a
  obtain ⟨o,s,j,b⟩:=t
  cases o <;> cases s <;> cases j <;> cases b <;>
    simp [π,l,θ,η,v,a,velocidadDelPerfil,coefDelPerfil,coefInverso,monoCuatro,
      pendienteTemporal,velocidadCuatro,factoresPatron,factorTemporal,velocidadTemporal,derivadaCoef,productRule] <;> ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.derivada_del_tensor
#print axioms ArticuloA.Historias.estado_del_tensor
#print axioms ArticuloA.Historias.pendiente_fisica_del_tensor
