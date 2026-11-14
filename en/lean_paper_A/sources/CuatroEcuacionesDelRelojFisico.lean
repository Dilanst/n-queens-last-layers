import CancelacionAdjuntaEnElEstadoE2
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Inversa
noncomputable section

/-- Identification of the scalar adjoint equations with the genuine
per-cell and per-line data of one stopped E2 state. -/
theorem cuatro_ecuaciones_en_region {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (e : Cell n) (u : Vertex) (y : ℝ) :
    let N:=(n:ℝ)*(A.c:ℝ)
    let z:=(A.z:ℝ)
    let π:=(A.piN e:ℝ)/n
    let p:=(A.p u:ℝ)
    let α:=(↑(A.time⁻¹/(n:ℝ≥0)):ℝ)
    let β:=(intensidadIdeal A u false:ℝ)
    let k:=(↑(A.birth e/(n:ℝ≥0)^2):ℝ)
    (-π/(N*z^4)+4*π*y/(N*z^5))+k-4*α*(π*y/z^4)=0 ∧
    (-p/(N*z)+p*y/(N*z^2))+β-α*(p*y/z)=0 := by
  intro N z π p α β k
  have np : (n:ℝ)≠0 := by
    have h:=A.sizePos; rw [ns_real] at h; change (n:ℝ≥0) ≠ 0 at h
    exact fun eq => h (NNReal.coe_injective (by simpa using eq))
  have time : (A.c:ℝ)*z≠0 := by
    have h : A.c*A.z≠0 := A.clockPos
    exact fun eq => h (NNReal.coe_injective (by simpa [z] using eq))
  have cp:=left_ne_zero_of_mul time
  have zp:=right_ne_zero_of_mul time
  have nN : N≠0 := mul_ne_zero np cp
  have four : fourth masas A.z=A.z^4 := by change (A.z*A.z)*A.z*A.z=_; ring
  have a : α=1/(N*z) := by
    change (↑((A.c*A.z)⁻¹/(n:ℝ≥0)):ℝ)=1/((n:ℝ)*(A.c:ℝ)*(A.z:ℝ))
    push_cast; field_simp [np,cp,show (A.z:ℝ)≠0 from zp]; ring
  have br : β=p/(N*z) := by
    change (↑(((A.c*A.z)⁻¹*A.p u)/(n:ℝ≥0)):ℝ)=(A.p u:ℝ)/((n:ℝ)*(A.c:ℝ)*(A.z:ℝ))
    push_cast; field_simp [np,cp,show (A.z:ℝ)≠0 from zp]; ring; simp
  have kr : k=π/(N*z^4) := by
    change (↑(((A.c*fourth masas A.z)⁻¹*A.piN e)/(n:ℝ≥0)^2):ℝ)=
      ((A.piN e:ℝ)/n)/((n:ℝ)*(A.c:ℝ)*(A.z:ℝ)^4)
    rw [four]; push_cast; field_simp [np,cp,show (A.z:ℝ)≠0 from zp]; ring; simp
  rw [a,br,kr]
  exact ArticuloA.Inversa.factores N z y π p nN zp

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuatro_ecuaciones_en_region
