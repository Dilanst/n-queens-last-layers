import DistanciaDeDensidadesPorElTrabajo
import DisipacionDeLaRamaReescalada
import BandaDelValorDelOptimo
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil Filter
local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance

theorem banda_del_normalizador {P p x b κ M L} (e : EulerFisica P p x b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (m1 : 1≤M) (hx : (x:ℝ)≤1/2) : (1/2)/M^4≤b ∧ b≤1/κ^4 := by
  have low:=cota_inferior_del_coeficiente e sp kp m1 hx
  exact ⟨(by convert low using 1; ring),techo_desde_la_masa e sp kp⟩

def constanteDiferenciaDensa (κ M : ℝ) :=
  (1/κ^4*M^4)*(2*(|Real.log ((1/2)/M^4)|+|Real.log (1/κ^4)|)+2*M*(2*(|Real.log κ|+|Real.log M|)))

theorem modulo_L1_de_la_densidad_fisica {P Q p q x y b c κ M L}
    (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L)
    (kp : 0<κ) (m1 : 1≤M) (lp : 0≤L) (hx : (x:ℝ)≤1/2) (hy : (y:ℝ)≤1/2) :
    (distanciaTableros P Q)^2≤constanteDiferenciaDensa κ M*|(y:ℝ)-x| := by
  let m:=(1/2:ℝ)/M^4
  let B:=1/κ^4
  have mp : 0<m := div_pos (by norm_num) (pow_pos (zero_lt_one.trans_le m1) 4)
  have Bp : 0<B := by dsimp [B]; positivity
  have cx:=banda_del_normalizador ex sp kp m1 hx
  have cy:=banda_del_normalizador ey sq kp m1 hy
  have bn {v : ℝ} (a : m≤v) (h : v≤B) : |Real.log v|≤|Real.log m|+|Real.log B| :=
    abs_le.mpr ⟨by linarith [Real.log_le_log mp a,neg_abs_le (Real.log m),abs_nonneg (Real.log B)],
      by linarith [Real.log_le_log (mp.trans_le a) h,le_abs_self (Real.log B),abs_nonneg (Real.log m)]⟩
  have dif : |Real.log b-Real.log c|≤2*(|Real.log m|+|Real.log B|) :=
    (abs_sub _ _).trans (by linarith only [bn cx.1 cx.2,bn cy.1 cy.2])
  have band {T r z v} (e : EulerFisica T r z v) (s : ControlEspacial r κ M L) (lower : m≤v) (upper : v≤B) :
      ∀ᵐ z ∂cuadrado,m*κ^4≤(T.ν z:ℝ) ∧ (T.ν z:ℝ)≤B*M^4 :=
    (densidad_en_banda e s kp).mono (fun _ h=>⟨(mul_le_mul_of_nonneg_right lower (by positivity)).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right upper (by positivity))⟩)
  have d:=distancia_cuadrada_acotada P Q (mul_pos mp (pow_pos kp 4)) (band ex sp cx.1 cx.2) (band ey sq cy.1 cy.2)
  have w:=trabajo_de_la_rama_acotado ex ey sp sq kp lp
  apply d.trans ((mul_le_mul_of_nonneg_left (w.trans
    (mul_le_mul_of_nonneg_left (add_le_add_right dif _) (abs_nonneg _))) (mul_nonneg Bp.le (by positivity))).trans_eq _)
  unfold constanteDiferenciaDensa; dsimp only [m,B]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.banda_del_normalizador
#print axioms ArticuloA.Historias.modulo_L1_de_la_densidad_fisica
