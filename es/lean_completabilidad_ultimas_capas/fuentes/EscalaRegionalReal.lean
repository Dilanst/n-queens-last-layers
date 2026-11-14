import ConcentracionCoordenadaE2
import DerivaVirtualRegional
import Mathlib.Tactic.FieldSimp
namespace ArticuloA.RealFinita
open ArticuloA ArticuloA.Trayectoria ArticuloA.Trayectoria.E2 E2.Regular E2.Regular.Region ProfileKernel Adjunto Control
open scoped NNReal

private theorem cost_igual (i m e : ℝ≥0) :
    cost masas i m e = i*(2*m+m^2)*e := by
  change i*((m*e+m*e)+m*(m*e)) = _
  ring

/-- A common coefficient at a fixed regularity floor. The hypotheses on
eps, off and bal use normalized coordinate errors. -/
theorem escala_marginal {n} {x : State n} {w : ColorWeights ℝ≥0}
    (A : Region masas x w (·⁻¹)) (S E : ℝ≥0)
    (track : S*A.eps ≤ E)
    (quad : S*A.off ≤ 1) (balance : S*A.bal ≤ 1) :
    S*A.combined ≤ ((A.l*A.l)⁻¹*(2*A.M+A.M^2)*2 + A.l⁻¹)*(E+1) := by
  have H := A.low
  have lp : A.l ≠ 0 := A.floorPos
  have hp : 0 < A.l := lt_of_le_of_ne bot_le (Ne.symm lp)
  have bound : (A.time)⁻¹ ≤ A.l⁻¹ := inv_anti₀ hp H
  let Z := (A.l*A.l)⁻¹*(2*A.M+A.M^2)
  have form : A.combined = Z*A.eps + Z*(A.eps+A.off) + A.time⁻¹*A.bal := by
    change cost masas (A.l*A.l)⁻¹ A.M A.eps + cost masas (A.l*A.l)⁻¹ A.M (A.eps+A.off) + _ = _
    rw [cost_igual,cost_igual]; rfl
  rw [form]
  change _ ≤ (Z*2+A.l⁻¹)*(E+1)
  calc _ = Z*(S*A.eps)+Z*(S*A.eps+S*A.off)+A.time⁻¹*(S*A.bal) := by ring
       _ ≤ Z*E+Z*(E+1)+A.l⁻¹*1 :=
         add_le_add (add_le_add (mul_le_mul_left' track _) (mul_le_mul_left' (add_le_add track quad) _))
           (mul_le_mul bound balance (zero_le _) (zero_le _))
       _ ≤ (Z*E+Z*(E+1)+A.l⁻¹*1) + (Z+A.l⁻¹*E) := le_add_of_nonneg_right (zero_le _)
       _ = _ := by ring

/-- Mean decrement of U_f on the actual kernel. In physical units its
error relative to U/(N-t) has the scale (E+1)/n. -/
theorem deriva_de_familia {n} {x : State n} {w : ColorWeights ℝ≥0}
    (A : Region masas x w (·⁻¹)) (f : Fin 4) (E C : ℝ≥0)
    (tracking : (n:ℝ≥0)*A.eps ≤ E)
    (off : (n:ℝ≥0)*A.off ≤ 1) (bal : (n:ℝ≥0)*A.bal ≤ 1)
    (mass : Cart.part masas x w f ≤ (n:ℝ≥0)*C) :
    let U := Cart.part masas x w f
    let row := choices masas x w (·⁻¹)
    let Λ := (A.l*A.l)⁻¹*(2*A.M+A.M^2)*2 + A.l⁻¹
    within masas ((n:ℝ≥0)*avg masas row (lostWeight masas x w f))
        ((n:ℝ≥0)*(U*((n:ℝ≥0)⁻¹*A.time⁻¹))) (C*Λ*(E+1)) := by
  intro U row Λ
  have nz : (n:ℝ≥0) ≠ 0 := by
    have H := A.sizePos; rw [ns_real] at H; exact H
  have data := family_drift A f (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
  dsimp only at data
  simp only [ns_real] at data
  have near := scale masas (n:ℝ≥0) data
  apply grow masas near
  change (n:ℝ≥0)*(U*((n:ℝ≥0)⁻¹*A.combined)) ≤ C*Λ*(E+1)
  have H := escala_marginal A (n:ℝ≥0) E tracking off bal
  calc _ = U*A.combined := by field_simp [nz]
       _ ≤ ((n:ℝ≥0)*C)*A.combined := mul_le_mul_right' mass _
       _ = C*((n:ℝ≥0)*A.combined) := by ring
       _ ≤ C*(Λ*(E+1)) := mul_le_mul_left' H _
       _ = _ := by ring
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.escala_marginal
#print axioms ArticuloA.RealFinita.deriva_de_familia
