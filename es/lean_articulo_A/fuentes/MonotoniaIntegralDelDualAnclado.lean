import CoercividadEnElCuadrado
import AdjuncionDeLasCuatroMarginales
open MeasureTheory Set
open scoped ENNReal
namespace ArticuloA.Perfil
noncomputable section

/-- Secant inequality for the exponential, including a coefficient held fixed. -/
theorem incremento_exponencial {u v b m : ℝ} (bp : 0≤b)
    (floorU : m≤b*Real.exp u) (floorV : m≤b*Real.exp v) :
    m*(v-u)^2≤b*(Real.exp v-Real.exp u)*(v-u) := by
  have ordered (x y : ℝ) (ord : x≤y) (low : m≤b*Real.exp x) :
      m*(y-x)^2≤b*(Real.exp y-Real.exp x)*(y-x) := by
    have p:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y-x)) (Real.exp_pos x).le
    rw [←Real.exp_add,show x+(y-x)=y by ring] at p
    have sec : Real.exp x*(y-x)≤Real.exp y-Real.exp x := by linarith
    have a:=mul_le_mul_of_nonneg_left sec bp
    have k:=mul_le_mul_of_nonneg_right low (sub_nonneg.mpr ord)
    apply (show m*(y-x)^2=(m*(y-x))*(y-x) by ring).le.trans
    exact mul_le_mul_of_nonneg_right (k.trans (by linarith only [a])) (sub_nonneg.mpr ord)
  rcases le_total u v with le|le
  · exact ordered u v le floorU
  · nlinarith only [ordered v u le floorV]

def trabajoExp {X : Type*} [MeasurableSpace X] (μ : Measure X) (u w : X→ℝ) (b : ℝ) :=
  ∫ z,b*(Real.exp (u z+w z)-Real.exp (u z))*w z ∂μ

theorem trabajo_controla_la_energia {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u w : X→ℝ) (b m : ℝ) (bp : 0≤b)
    (sq : Integrable (fun z => (w z)^2) μ)
    (work : Integrable (fun z => b*(Real.exp (u z+w z)-Real.exp (u z))*w z) μ)
    (floor : ∀ᵐ z ∂μ,m≤b*Real.exp (u z) ∧ m≤b*Real.exp (u z+w z)) :
    m*(energia μ w).toReal≤trabajoExp μ u w b := by
  have eq : (∫ z,(w z)^2 ∂μ)=(energia μ w).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) sq.aestronglyMeasurable
  rw [←eq,←integral_const_mul]
  apply integral_mono_ae (sq.const_mul _) work
  filter_upwards [floor] with z fl
  simpa only [add_sub_cancel_left] using incremento_exponencial bp fl.1 fl.2

/-- Finite differences on the actual square. D and A retain their own line
penalties even at full density. Either R or C stays fixed pointwise. -/
theorem dual_anclado_por_diferencias (vertical : Bool) (r d a : ℝ→ℝ)
    (hr : Measurable r) (hd : Measurable d) (ha : Measurable a)
    (uQ : ℝ×ℝ→ℝ) (uD uA : ℝ→ℝ) (b c κ : ℝ) (bp : 0≤b) (cp : 0≤c) (kp : 0≤κ)
    (q2 : Integrable (fun z => (sumaLevantada vertical r d a z)^2) cuadrado)
    (d2 : Integrable (fun t => (d t)^2) diag) (a2 : Integrable (fun t => (a t)^2) anti)
    (qw : Integrable (fun z => b*(Real.exp (uQ z+sumaLevantada vertical r d a z)-Real.exp (uQ z))*
      sumaLevantada vertical r d a z) cuadrado)
    (dw : Integrable (fun t => 1*(Real.exp (uD t+d t)-Real.exp (uD t))*d t) diag)
    (aw : Integrable (fun t => 1*(Real.exp (uA t+a t)-Real.exp (uA t))*a t) anti)
    (qfloor : ∀ᵐ z ∂cuadrado,c≤b*Real.exp (uQ z) ∧ c≤b*Real.exp (uQ z+sumaLevantada vertical r d a z))
    (dfloor : ∀ᵐ t ∂diag,κ≤Real.exp (uD t) ∧ κ≤Real.exp (uD t+d t))
    (afloor : ∀ᵐ t ∂anti,κ≤Real.exp (uA t) ∧ κ≤Real.exp (uA t+a t)) :
    min (c/2) (κ/5)*((energia unidad r).toReal+(energia diag d).toReal+(energia anti a).toReal)≤
      trabajoExp cuadrado uQ (sumaLevantada vertical r d a) b+
      trabajoExp diag uD d 1+trabajoExp anti uA a 1 := by
  have finite {X : Type} [MeasurableSpace X] {μ : Measure X} (w : X→ℝ)
      (ok : Integrable (fun t => (w t)^2) μ) : energia μ w≠∞ := by
    have h := ok.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))] at h
    exact h.ne
  apply coercividad_integral vertical r d a hr hd ha c κ _ cp kp (finite (μ:=cuadrado) _ q2)
    (finite (μ:=diag) d d2) (finite (μ:=anti) a a2)
  have q:=trabajo_controla_la_energia uQ (sumaLevantada vertical r d a) b c bp q2 qw qfloor
  have s:=trabajo_controla_la_energia uD d 1 κ zero_le_one d2 dw (by simpa using dfloor)
  have t:=trabajo_controla_la_energia uA a 1 κ zero_le_one a2 aw (by simpa using afloor)
  linarith only [q,s,t]

end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.dual_anclado_por_diferencias
