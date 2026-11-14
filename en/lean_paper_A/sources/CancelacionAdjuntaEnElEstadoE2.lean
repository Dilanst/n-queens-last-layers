import AdjuntoPonderadoDeLosDieciseisPatrones
import ErrorDeCadaLineaInversa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Inversa
noncomputable section

/-- Sum of the sixteen ideal drifts cancels the continuous time derivative of
the coefficient at one physical state, for the four scalar adjoint equations. -/
theorem cancelacion_del_adjunto_fisico {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (e f : Cell n) (θ₁ θ₂ η₁ η₂ θ₁' θ₂' η₁' η₂' : ℝ) :
    let k:=fun e => (↑(A.birth e/(n:ℝ≥0)^2):ℝ)
    let α:=(↑(A.time⁻¹/(n:ℝ≥0)):ℝ)
    let β:=fun u => (intensidadIdeal A u false:ℝ)
    let dest:=fun i => lineLabel (corners (e,f)).2 i
    let O:=fun e => estadoEscalar (estadoFuente X e true)
    let H:=fun e => estadoEscalar (estadoFuente X e false)
    let V:=fun i => estadoEscalar (estadoMarca X e f i false)
    let T:=fun i => estadoEscalar (estadoMarca X e f i true)
    θ₁'+k e-4*α*θ₁=0 → θ₂'+k f-4*α*θ₂=0 →
    η₁'+β (dest 2)-α*η₁=0 → η₂'+β (dest 3)-α*η₂=0 →
    productRule (pairForm (O e) (H e) θ₁) (pairForm (O f) (H f) θ₂)
        (pairForm (V 2) (T 2) (-η₁)) (pairForm (V 3) (T 3) (-η₂))
        (θ₁'*H e) (θ₂'*H f) (-η₁'*T 2) (-η₂'*T 3)+
      ∑ t : CuatroMarcas,coefInverso θ₁ θ₂ η₁ η₂ t*operadorInverso X e f t.1 t.2.1 t.2.2.1 t.2.2.2
        k (fun u b => (intensidadIdeal A u b:ℝ))=0 := by
  intro k α β dest O H V T h₁ h₂ h₃ h₄
  have rates : (fun u b => (intensidadIdeal A u b:ℝ))=(fun u (b : Bool) => if b then α else β u) := by
    funext u b; cases b <;> rfl
  rw [rates,operador_ideal_en_el_tensor]
  exact adjunto_del_par (O e) (H e) (O f) (H f) (V 2) (T 2) (V 3) (T 3) θ₁ θ₂ η₁ η₂
    α (k e) (k f) (β (dest 2)) (β (dest 3)) θ₁' θ₂' η₁' η₂' h₁ h₂ h₃ h₄

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cancelacion_del_adjunto_fisico
