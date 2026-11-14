import CrucesDeLaConfiguracion
import LimiteDesdeDesviacionesFisicas
open Filter
open scoped Topology BigOperators
namespace ArticuloA.Limites
noncomputable section

/-- Signed weights are allowed. The inverse law lives at h-1, also when h=1. -/
theorem media_directa_desde_inversa (h : ℕ) (hh : h≠0) (w : (n : ℕ) → Cell n → ℝ)
    {F B : ℝ} (niveles : ∀ᶠ n in atTop, count n (n-h)≠0 ∧ count n (n-h+1)≠0)
    (fraccion : Tendsto (fun n => fracReal n h) atTop (𝓝 F))
    (inversa : Tendsto (fun n => mediaI n h (w n)) atTop (𝓝 B)) :
    Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 (F*B)) := by
  have cv := (fraccion.mul inversa).div (factor_nivel h) one_ne_zero
  rw [div_one] at cv
  apply cv.congr'
  filter_upwards [niveles,eventually_gt_atTop (0:ℕ)] with n levels pos
  apply (div_eq_iff (div_ne_zero (by exact_mod_cast Nat.succ_ne_zero (n-h))
    (by exact_mod_cast pos.ne'))).mpr
  rw [mul_comm (mediaD _ _ _)]
  exact relacion_fisica _ pos.ne' hh levels.1 levels.2

theorem estructura_en_media (h : ℕ) (hh : h≠0) (w : (n : ℕ) → Cell n → ℝ)
    (t : (n : ℕ) → Cell n → ℝ) {b L : ℝ} (bp : 0<b)
    (niveles : ∀ᶠ n in atTop, count n (n-h)≠0 ∧ count n (n-h+1)≠0)
    (fraccion : Tendsto (fun n => fracReal n h) atTop (𝓝 (1/b)))
    (inversa : Tendsto (fun n => mediaI n h (w n)) atTop (𝓝 (b*L)))
    (reponderacion : Tendsto (fun n => promedioNivel n (n-h) (fun p => mediaCruces p h (t n))-mediaD n h (w n))
      atTop (𝓝 0)) :
    Tendsto (fun n => promedioNivel n (n-h) (fun p => mediaCruces p h (t n))) atTop (𝓝 L) := by
  have D := media_directa_desde_inversa h hh w niveles fraccion inversa
  have eq : (1/b)*(b*L)=L := by field_simp
  rw [eq] at D
  simpa using reponderacion.add D
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.estructura_en_media
