import CotasDeLasMediasFisicas
import TransferenciaDesdeHistorias
import DobleCuentaReal
open Filter
open scoped Topology BigOperators
namespace ArticuloA.Limites
noncomputable section

/-- Probability under the uniform law on the actual legal layer. -/
def desviacion (n q : ℕ) (X : Placement n → ℝ) (a ε : ℝ) :=
  ∑ p ∈ nivel n q, if ε < |X p-a| then (count n q:ℝ)⁻¹ else 0

theorem media_desde_prob (q : ℕ → ℕ) (X : (n : ℕ) → Placement n → ℝ) (a M : ℝ)
    (valid : ∀ᶠ n in atTop, 0<count n (q n))
    (bound : ∀ᶠ n in atTop, ∀ p ∈ nivel n (q n), |X n p|≤M)
    (dev : ∀ ε>0, Tendsto (fun n => desviacion n (q n) (X n) a ε) atTop (𝓝 0)) :
    Tendsto (fun n => promedioNivel n (q n) (X n)) atTop (𝓝 a) := by
  let pur := fun (n : ℕ) (_ : Placement n) => (count n (q n):ℝ)⁻¹
  have nonneg : ∀ᶠ n in atTop, ∀ p ∈ nivel n (q n), 0 ≤ pur n p := by
    apply Eventually.of_forall; intro n p _; dsimp [pur]; positivity
  have one : ∀ᶠ n in atTop, ∑ p ∈ nivel n (q n), pur n p = 1 := by
    filter_upwards [valid] with n h
    have nz : (count n (q n):ℝ) ≠ 0 := by exact_mod_cast h.ne'
    simp [pur,cardinal_nivel,nz]
  have centered : ∀ᶠ n in atTop, ∀ p ∈ nivel n (q n), |X n p-a| ≤ M+|a| := by
    filter_upwards [bound] with n H
    intro p hp
    calc |X n p-a| = |X n p + -a| := rfl
         _ ≤ |X n p| + |-a| := abs_add_le _ _
         _ ≤ M+|a| := by rw [abs_neg]; exact add_le_add_right (H p hp) _
  have H := Entropia.media_del_nivel (fun n => nivel n (q n)) pur X a (M+|a|) nonneg one centered dev
  apply H.congr
  intro n
  simp only [promedioNivel,pur,div_eq_mul_inv,mul_comm (count n (q n):ℝ)⁻¹]
  rw [Finset.sum_mul]

/-- The remaining probabilistic hypotheses apply to the physical observables
on two different uniform laws. Boundedness of weights implies both required
uniform-integrability estimates by finite counting. -/
theorem limite_por_eventos (h : ℕ) (hh : 0<h) (w : (n : ℕ) → Cell n → ℝ)
    (b M : ℝ) (hb : 0<b) (hm : 0≤M) (cap : ∀ n e, |w n e|≤M)
    (layers : ∀ᶠ n in atTop, 0<count n (n-h) ∧ 0<count n (n-h+1))
    (directa : ∀ ε>0, Tendsto (fun n => desviacion n (n-h) (Dobs n h (w n)) 1 ε) atTop (𝓝 0))
    (inversa : ∀ ε>0, Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (w n)) b ε) atTop (𝓝 0)) :
    Tendsto (fun n => fracReal n h) atTop (𝓝 (1/b)) := by
  have HD := media_desde_prob (fun n => n-h) (fun n => Dobs n h (w n)) 1 M (layers.mono (fun _ H => H.1))
    ((eventually_ge_atTop h).mono (fun n nh => directa_acotada n h nh hh (w n) M hm (cap n))) directa
  have HI := media_desde_prob (fun n => n-h+1) (fun n => Iobs n h (w n)) b M (layers.mono (fun _ H => H.2))
    ((eventually_ge_atTop h).mono (fun n nh => inversa_acotada n h nh hh (w n) M hm (cap n))) inversa
  exact limite_fisico h hh.ne' w hb (layers.mono (fun _ H => ⟨H.1.ne',H.2.ne'⟩))
    (HD.congr (fun n => (directa_uniforme n h (w n)).symm))
    (HI.congr (fun n => (inversa_uniforme n h (w n)).symm))
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.media_desde_prob
#print axioms ArticuloA.Limites.limite_por_eventos
