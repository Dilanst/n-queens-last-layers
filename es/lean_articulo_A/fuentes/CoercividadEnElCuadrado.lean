import ElevacionesDelCuadrado
import EnergiaDeTresComponentes
open MeasureTheory Set
open scoped ENNReal
namespace ArticuloA.Perfil
noncomputable section
def diag := volume.restrict (Icc (-1:ℝ) 1)
def anti := volume.restrict (Icc (0:ℝ) 2)
def transversal (vertical : Bool) (z : ℝ×ℝ) := if vertical then z.2 else z.1
def sumaLevantada (vertical : Bool) (r d a : ℝ→ℝ) (z : ℝ×ℝ) :=
  r (transversal vertical z)+d (z.1-z.2)+a (z.1+z.2)

theorem energia_de_la_transversal (vertical : Bool) (r d a : ℝ→ℝ)
    (hr : Measurable r) (hd : Measurable d) (ha : Measurable a) :
    energia unidad r≤2*energia cuadrado (sumaLevantada vertical r d a)+4*(energia diag d+energia anti a) := by
  have med : Measurable (transversal vertical) := by
    cases vertical <;> first | exact measurable_snd | exact measurable_fst
  have obs := integral_tres cuadrado (r ∘ transversal vertical)
    (fun z => d (z.1-z.2)) (fun z => a (z.1+z.2)) (hr.comp med)
    (hd.comp (measurable_fst.sub measurable_snd)) (ha.comp (measurable_fst.add measurable_snd))
  have eq : energia cuadrado (r ∘ transversal vertical)=energia unidad r := by
    cases vertical
    · exact levantar_fila (e2 ∘ r) (e2_med.comp hr)
    · exact levantar_columna (e2 ∘ r) (e2_med.comp hr)
  rw [eq] at obs
  exact obs.trans (add_le_add_left (mul_le_mul_left' (add_le_add
    (levantar_diagonal (e2 ∘ d) (e2_med.comp hd)) (levantar_antidiagonal (e2 ∘ a) (e2_med.comp ha))) 4) _)

theorem coercividad_integral (vertical : Bool) (r d a : ℝ→ℝ) (hr : Measurable r)
    (hd : Measurable d) (ha : Measurable a) (c κ H : ℝ) (cp : 0≤c) (kp : 0≤κ)
    (fs : energia cuadrado (sumaLevantada vertical r d a)≠∞) (fd : energia diag d≠∞) (fa : energia anti a≠∞)
    (hess : κ*((energia diag d).toReal+(energia anti a).toReal)+
      c*(energia cuadrado (sumaLevantada vertical r d a)).toReal≤H) :
    min (c/2) (κ/5)*((energia unidad r).toReal+(energia diag d).toReal+(energia anti a).toReal)≤H := by
  have alg := energia_de_la_transversal vertical r d a hr hd ha
  have fft := ENNReal.add_ne_top.mpr ⟨fd,fa⟩
  have t1 := ENNReal.mul_ne_top (a:=(2:ℝ≥0∞)) ENNReal.ofNat_ne_top fs
  have t2 := ENNReal.mul_ne_top (a:=(4:ℝ≥0∞)) ENNReal.ofNat_ne_top fft
  have fin : 2*energia cuadrado (sumaLevantada vertical r d a)+4*(energia diag d+energia anti a)≠∞ := by
    exact ENNReal.add_ne_top.mpr ⟨t1,t2⟩
  have real := ENNReal.toReal_mono fin alg
  rw [ENNReal.toReal_add t1 t2,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_add fd fa] at real
  norm_num at real
  let t := min (c/2) (κ/5)
  have t0 : 0≤t := le_min (by positivity) (by positivity)
  have ct : 2*t≤c := by have := min_le_left (c/2) (κ/5); dsimp [t]; linarith
  have kt : 5*t≤κ := by have := min_le_right (c/2) (κ/5); dsimp [t]; linarith
  have q := mul_le_mul_of_nonneg_left real t0
  have s := mul_le_mul_of_nonneg_right ct (ENNReal.toReal_nonneg (a:=energia cuadrado (sumaLevantada vertical r d a)))
  have p := mul_le_mul_of_nonneg_right kt (add_nonneg (ENNReal.toReal_nonneg (a:=energia diag d))
    (ENNReal.toReal_nonneg (a:=energia anti a)))
  change t*_≤H
  linarith only [hess,q,s,p]
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.energia_de_la_transversal
#print axioms ArticuloA.Perfil.coercividad_integral
