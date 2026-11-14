import DiferenciaDelProductoDeTresFactores
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
theorem oscilacion_de_integrales_de_tres (A B : ℝ→Fin 3→ℝ) {M l v : ℝ} (nn : 0≤l) (M0 : 0≤M)
    (ab : ∀ t j,‖A t j‖≤M) (bb : ∀ t j,‖B t j‖≤M)
    (am : ∀ j,Measurable (fun t=>A t j)) (bm : ∀ j,Measurable (fun t=>B t j)) :
    let U := fun t=>A t 0*A t 1*A t 2
    let W := fun t=>B t 0*B t 1*B t 2
    |(∫ t in (0:ℝ)..l,U t)-(∫ t in (0:ℝ)..v,W t)| ≤
      M^2*(∑ j : Fin 3,∫ t in (0:ℝ)..l,|A t j-B t j|)+M^3*|l-v| := by
  dsimp only
  let U := fun t=>A t 0*A t 1*A t 2
  let W := fun t=>B t 0*B t 1*B t 2
  let V (j : Fin 3) (t : ℝ):=|A t j-B t j|
  have bound {g : ℝ→ℝ} (gm : Measurable g) {D : ℝ} (bd : ∀ t,‖g t‖≤D) (a b : ℝ) :
      IntervalIntegrable g volume a b :=
    (intervalIntegrable_const (c:=D)).mono_fun' gm.aestronglyMeasurable (Eventually.of_forall bd)
  have prod {f : Fin 3→ℝ} (bf : ∀ j,‖f j‖≤M) : ‖f 0*f 1*f 2‖≤M^3 := by
    rw [norm_mul,norm_mul,pow_succ,pow_two]
    exact mul_le_mul (mul_le_mul (bf 0) (bf 1) (norm_nonneg _) M0) (bf 2) (norm_nonneg _) (mul_nonneg M0 M0)
  have ui := bound (((am 0).mul (am 1)).mul (am 2)) (fun t=>prod (ab t))
  have wi := bound (((bm 0).mul (bm 1)).mul (bm 2)) (fun t=>prod (bb t))
  have vi j : IntervalIntegrable (V j) volume 0 l :=
    ((bound (am j) (fun t=>ab t j) 0 l).sub (bound (bm j) (fun t=>bb t j) 0 l)).norm
  have vs : IntervalIntegrable (fun t=>∑ j : Fin 3,V j t) volume 0 l := by
    simpa only [←Finset.sum_apply] using (IntervalIntegrable.sum (f:=V) Finset.univ (fun j _=>vi j))
  have central : |(∫ t in (0:ℝ)..l,U t)-∫ t in (0:ℝ)..l,W t|≤M^2*∑ j : Fin 3,∫ t in (0:ℝ)..l,V j t := by
    rw [←intervalIntegral.integral_sub (ui _ _) (wi _ _)]
    apply (intervalIntegral.abs_integral_le_integral_abs nn).trans
    rw [←intervalIntegral.integral_finset_sum (fun j _=>vi j),←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on nn ((ui _ _).sub (wi _ _)).norm (vs.const_mul _)
    intro t _
    simpa only [Fin.sum_univ_three,U,W,V] using diferencia_producto_tres (A t) (B t) (ab t) (bb t)
  have edge : |(∫ t in (0:ℝ)..l,W t)-∫ t in (0:ℝ)..v,W t| ≤ M^3*|l-v| := by
    rw [intervalIntegral.integral_interval_sub_left (wi _ _) (wi _ _)]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (f:=W) (fun t _=>prod (bb t))
  exact (abs_sub_le _ (∫ t in (0:ℝ)..l,W t) _).trans (add_le_add central edge)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscilacion_de_integrales_de_tres
