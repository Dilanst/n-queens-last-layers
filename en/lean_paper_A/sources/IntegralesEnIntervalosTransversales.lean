import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory
open scoped Interval
theorem masa_no_aumenta_bajo_transversal {f : ℝ→ℝ} {l u a c d : ℝ}
    (hlu : l≤u) (ha : a∈Icc l u) (hb : c*d+a∈Icc l u) (hc : 1≤|c|)
    (hn : ∀ y,0≤f y) (hi : IntervalIntegrable f volume l u) :
    (∫ t in (0:ℝ)..d,f (c*t+a))≤∫ y in l..u,f y := by
  have cn : c≠0 := by intro he; norm_num [he] at hc
  have inclusion : Ι a (c*d+a) ⊆ Ι l u := by
    rw [uIoc_of_le hlu]
    intro y hy
    exact ⟨lt_of_le_of_lt (le_min ha.1 hb.1) hy.1,hy.2.trans (max_le ha.2 hb.2)⟩
  have mono:=intervalIntegral.abs_integral_mono_interval (μ:=volume) inclusion
    (Filter.Eventually.of_forall hn) hi
  have full : 0≤∫ y in l..u,f y := intervalIntegral.integral_nonneg_of_forall hlu hn
  rw [abs_of_nonneg full] at mono
  have invle : |c⁻¹|≤1 := by
    rw [abs_inv,inv_eq_one_div]
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hc)).mpr hc
  rw [intervalIntegral.integral_comp_mul_add f cn a,mul_zero,zero_add,smul_eq_mul]
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right invle (abs_nonneg _)).trans (by simpa using mono))

theorem cuadrado_media_de_cuerda {d : ℝ} (hd : d∈Icc 0 1) {f : ℝ→ℝ}
    (h1 : IntervalIntegrable f volume 0 d) (h2 : IntervalIntegrable (fun t=>f t^2) volume 0 d) :
    (∫ t in (0:ℝ)..d,f t)^2 ≤ ∫ t in (0:ℝ)..d,f t^2 := by
  let A:=∫ t in (0:ℝ)..d,f t
  have hs : ∀ t∈Icc 0 d,(2*A)*f t≤f t^2+A^2 :=
    fun t _ => by nlinarith [sq_nonneg (f t-A)]
  have h:=intervalIntegral.integral_mono_on hd.1 (h1.const_mul (2*A))
    (h2.add (intervalIntegrable_const (c:=A^2))) hs
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add h2 intervalIntegrable_const,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h
  change (2*A)*A≤_+d*A^2 at h
  exact by nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) (sq_nonneg A)]

theorem masa_absoluta_desde_energia {f : ℝ→ℝ} {l u a c d : ℝ} (hd : d∈Icc 0 1)
    (hlu : l≤u) (ha : a∈Icc l u) (hb : c*d+a∈Icc l u) (hc : 1≤|c|)
    (hi : IntervalIntegrable (fun y=>f y^2) volume l u)
    (h1 : IntervalIntegrable (fun t=>|f (c*t+a)|) volume 0 d)
    (h2 : IntervalIntegrable (fun t=>f (c*t+a)^2) volume 0 d) :
    (∫ t in (0:ℝ)..d,|f (c*t+a)|)≤Real.sqrt (∫ y in l..u,f y^2) := by
  have hsq : ∀ t : ℝ,|f (c*t+a)|^2=f (c*t+a)^2 := fun _=>sq_abs _
  have v:=cuadrado_media_de_cuerda hd h1 (by simpa only [hsq] using h2)
  simp only [hsq] at v
  have e:=masa_no_aumenta_bajo_transversal hlu ha hb hc (fun y=>sq_nonneg (f y)) hi
  exact Real.le_sqrt_of_sq_le (v.trans e)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_no_aumenta_bajo_transversal
#print axioms ArticuloA.Historias.cuadrado_media_de_cuerda
#print axioms ArticuloA.Historias.masa_absoluta_desde_energia
