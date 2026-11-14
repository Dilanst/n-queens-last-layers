import TransferenciaAsintotica
import MediaDeObservablesAcotados
open Filter
open scoped BigOperators Topology
namespace ArticuloA.Entropia

/-- The comparison paths are successful. Restrict q to their support, leaving
its original masses untouched. The bad event there is success AND terminal bad.
No independence of the terminal configuration and success is needed. -/
theorem malas_uniformes {Ω : ℕ → Type*} (S : (n : ℕ) → Finset (Ω n))
    (p q : (n : ℕ) → Ω n → ℝ) (bad : (n : ℕ) → Ω n → Bool)
    (hp : ∀ᶠ n in atTop, ∀ i ∈ S n, 0 < p n i) (hq : ∀ᶠ n in atTop, ∀ i ∈ S n, 0 < q n i)
    (one : ∀ᶠ n in atTop, ∑ i ∈ S n, p n i = 1) (sub : ∀ᶠ n in atTop, ∑ i ∈ S n, q n i ≤ 1)
    (u d : ℕ → ℝ) (projection : ∀ᶠ n in atTop, u n = ∑ i ∈ S n, if bad n i then p n i else 0)
    (nonneg : ∀ n, 0 ≤ d n) (small : Tendsto (fun n => d n/(n:ℝ)) atTop (𝓝 0))
    (KL : ∀ᶠ n in atTop, ∑ i ∈ S n, p n i * Real.log (p n i / q n i) ≤ d n)
    {c : ℝ} (hc : 0<c) (rare : ∀ᶠ n in atTop,
      (∑ i ∈ S n, if bad n i then q n i else 0) ≤ Real.exp (-(c*n))) :
    Tendsto u atTop (𝓝 0) := by
  have nneg : ∀ᶠ n in atTop, 0 ≤ u n := by
    filter_upwards [hp,projection] with n H proj
    rw [proj]
    apply Finset.sum_nonneg
    intro i hi; split <;> first | exact (H i hi).le | exact le_rfl
  apply transferencia u d hc nneg small
  filter_upwards [KL,rare,hp,hq,one,sub,projection,nneg] with n kl r hP hQ h₁ h₂ proj nn
  have product := mul_le_mul_of_nonneg_right r (Real.exp_pos (c*n)).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at product
  have B := coste_binario (S n) (p n) (q n) (bad n) (c*n) hP hQ h₁ h₂ product
  rw [←proj] at B
  linarith [mul_nonneg nn (nonneg n)]
/-- Bounded signed observables after the bad-event probabilities have been
transferred. Probabilities are positive; the observable may change sign. -/
theorem media_del_nivel {Ω : ℕ → Type*} (S : (n : ℕ) → Finset (Ω n))
    (p X : (n : ℕ) → Ω n → ℝ) (a M : ℝ)
    (nn : ∀ᶠ n in atTop, ∀ i ∈ S n, 0 ≤ p n i) (one : ∀ᶠ n in atTop, ∑ i ∈ S n, p n i = 1)
    (cap : ∀ᶠ n in atTop, ∀ i ∈ S n, |X n i-a| ≤ M)
    (small : ∀ ε > 0, Tendsto (fun n => ∑ i ∈ S n,
      if ε < |X n i-a| then p n i else 0) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ S n, p n i*X n i) atTop (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have ep : 0 < ε/2 := half_pos he
  let m := fun n => ∑ i ∈ S n, if ε/2 < |X n i-a| then p n i else 0
  have bnd : Tendsto (fun n => ε/2+M*m n) atTop (𝓝 (ε/2)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ε/2) atTop (𝓝 (ε/2))).add
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M)).mul (small _ ep))
  filter_upwards [(tendsto_order.mp bnd).2 ε (half_lt_self he),nn,one,cap] with n hn hn₁ hn₂ hn₃
  rw [Real.dist_eq]
  exact (media_acotada (S n) (p n) (X n) a M (ε/2) hn₁ hn₂ hn₃ ep.le).trans_lt hn
end ArticuloA.Entropia
#print axioms ArticuloA.Entropia.malas_uniformes
#print axioms ArticuloA.Entropia.media_del_nivel
