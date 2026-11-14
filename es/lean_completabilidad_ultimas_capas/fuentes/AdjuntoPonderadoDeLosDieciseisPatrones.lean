import OperadorIdealDelPatronInverso
import CompensadorInversoIdeal
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair Inversa
noncomputable section
open Classical

def monoCuatro (a b c d : Bool→ℝ) (t : CuatroMarcas) := a t.1*b t.2.1*c t.2.2.1*d t.2.2.2
def coefInverso (θ₁ θ₂ η₁ η₂ : ℝ) := monoCuatro
  (fun o => if o then 1 else θ₁) (fun v => if v then 1 else θ₂)
  (fun j => if j then -η₁ else 1) (fun l => if l then -η₂ else 1)
def estadoEscalar (P : Prop) : ℝ := (indicator P:ℝ)

theorem tensorizar_suma (a b c d : Bool→ℝ) (θ₁ θ₂ η₁ η₂ : ℝ) :
    ∑ t,coefInverso θ₁ θ₂ η₁ η₂ t*monoCuatro a b c d t =
      (a true+θ₁*a false)*(b true+θ₂*b false)*(c false-η₁*c true)*(d false-η₂*d true) := by
  change (∑ t : Bool × Bool × Bool × Bool,_) = _
  simp [Fintype.sum_prod_type,Fintype.sum_bool,coefInverso,monoCuatro]; ring

private theorem and_escalar (P Q : Prop) :
    estadoEscalar (P ∧ Q)=estadoEscalar P*estadoEscalar Q := by
  by_cases h:P <;> by_cases k:Q <;> simp [h,k,estadoEscalar,indicator]
private theorem guardia_escalar (P : Prop) (x : ℝ) : filtrarTasa P x=estadoEscalar P*x := by
  by_cases h:P <;> simp [filtrarTasa,h,estadoEscalar,indicator]

private theorem forma_ideal {n} (X : State n) (e f : Cell n) (t : CuatroMarcas) (α : ℝ)
    (k : Cell n→ℝ) (β : Vertex→ℝ) :
    let a:=fun o => estadoEscalar (estadoFuente X e o)
    let b:=fun v => estadoEscalar (estadoFuente X f v)
    let c:=fun j => estadoEscalar (estadoMarca X e f 2 j)
    let d:=fun l => estadoEscalar (estadoMarca X e f 3 l)
    let K:=fun a' k' (o : Bool) => if o then k'*a' false else -4*α*a' false
    let J:=fun c' β' (j : Bool) => if j then -α*c' true else -β'*c' true
    operadorInverso X e f t.1 t.2.1 t.2.2.1 t.2.2.2 k (fun u j => if j then α else β u)=
      monoCuatro (K a (k e)) b c d t+monoCuatro a (K b (k f)) c d t+
      monoCuatro a b (J c (β (lineLabel (corners (e,f)).2 2))) d t+
      monoCuatro a b c (J d (β (lineLabel (corners (e,f)).2 3))) t := by
  have off : estadoEscalar False=0 := by simp [estadoEscalar,indicator]
  obtain ⟨o,v,j,l⟩:=t
  cases o <;> cases v <;> cases j <;> cases l <;>
    simp only [operadorInverso,inserciones,sumaFuentes,sumaMetas,patronInverso,monoCuatro,
      Fin.sum_univ_four,Bool.true_eq_false,Bool.false_eq_true,eq_self,if_false,if_true,
      and_true,true_and,and_false,false_and,guardia_escalar,and_escalar,off,zero_mul] <;> ring

/-- Identification of the finite physical ideal operator with the product rule of
the four adjoint factors. This is an identity on the pre-move configuration. -/
theorem operador_ideal_en_el_tensor {n} (X : State n) (e f : Cell n) (α θ₁ θ₂ η₁ η₂ : ℝ)
    (k : Cell n→ℝ) (β : Vertex→ℝ) :
    let O:=fun e => estadoEscalar (estadoFuente X e true)
    let H:=fun e => estadoEscalar (estadoFuente X e false)
    let V:=fun i => estadoEscalar (estadoMarca X e f i false)
    let A:=fun i => estadoEscalar (estadoMarca X e f i true)
    ∑ t : CuatroMarcas,coefInverso θ₁ θ₂ η₁ η₂ t*
      operadorInverso X e f t.1 t.2.1 t.2.2.1 t.2.2.2 k (fun u j => if j then α else β u)=
      productRule (pairForm (O e) (H e) θ₁) (pairForm (O f) (H f) θ₂)
        (pairForm (V 2) (A 2) (-η₁)) (pairForm (V 3) (A 3) (-η₂))
        ((k e-4*α*θ₁)*H e) ((k f-4*α*θ₂)*H f)
        ((-β (lineLabel (corners (e,f)).2 2)+α*η₁)*A 2)
        ((-β (lineLabel (corners (e,f)).2 3)+α*η₂)*A 3) := by
  intro O H V A
  simp_rw [forma_ideal X e f _ α k β]
  simp only [mul_add,Finset.sum_add_distrib,tensorizar_suma,if_true,Bool.false_eq_true,if_false]
  dsimp only [O,H,V,A,productRule,pairForm]; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.operador_ideal_en_el_tensor
