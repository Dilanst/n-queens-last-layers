import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
private theorem descomposicion {a b c u v w K : ℝ}
    (hb : |b|≤K) (hc : |c|≤K) (hu : |u|≤K) (hv : |v|≤K) :
    |a*b*c-u*v*w|≤K^2*(|a-u|+|b-v|+|c-w|) := by
  have hk : 0≤K := (abs_nonneg b).trans hb
  have pair (x y : ℝ) (hx : |x|≤K) (hy : |y|≤K) : |x*y|≤K^2 := by
    rw [abs_mul,pow_two]; exact mul_le_mul hx hy (abs_nonneg _) hk
  have eid : a*b*c-u*v*w=b*c*(a-u)+u*c*(b-v)+u*v*(c-w) := by ring
  rw [eid]
  calc
    _ ≤ (|b*c*(a-u)|+|u*c*(b-v)|)+|u*v*(c-w)| := (abs_add_le ..).trans (add_le_add_right (abs_add_le ..) _)
    _ ≤ K^2*|a-u|+K^2*|b-v|+K^2*|c-w| := by
      rw [abs_mul (b*c),abs_mul (u*c),abs_mul (u*v)]
      gcongr
      · exact pair b c hb hc
      · exact pair u c hu hc
      · exact pair u v hu hv
    _ = _ := by ring

theorem diferencia_producto_tres (a u : Fin 3→ℝ) {K : ℝ}
    (ha : ∀ j,|a j|≤K) (hu : ∀ j,|u j|≤K) :
    |a 0*a 1*a 2-u 0*u 1*u 2|≤K^2*(|a 0-u 0|+|a 1-u 1|+|a 2-u 2|) :=
  descomposicion (ha 1) (ha 2) (hu 0) (hu 1)

theorem diferencia_exponencial_desde_arriba {a b K : ℝ}
    (ha : Real.exp a≤K) (hb : Real.exp b≤K) :
    |Real.exp a-Real.exp b|≤K*|a-b| := by
  have orden (x y : ℝ) (h : x≤y) (hy : Real.exp y≤K) :
      Real.exp y-Real.exp x≤K*(y-x) := by
    have e:=mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
    rw [←Real.exp_add,sub_add_cancel] at e
    calc
      _ ≤ Real.exp y*(y-x) := by linarith only [e]
      _ ≤ _ := mul_le_mul_of_nonneg_right hy (sub_nonneg.mpr h)
  rcases le_total a b with hab|hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hab)),abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using orden a b hab hb
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba)),abs_of_nonneg (sub_nonneg.mpr hba)]
    exact orden b a hba ha
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.diferencia_producto_tres
#print axioms ArticuloA.Historias.diferencia_exponencial_desde_arriba
