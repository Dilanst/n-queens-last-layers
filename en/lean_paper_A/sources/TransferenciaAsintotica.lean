import TransferenciaDeEvento
open Filter
open scoped Topology
namespace ArticuloA.Entropia

/-- The exponent lost by conditioning is d; this lemma is applied
after analysing transitions under the unconditioned process. -/
theorem exito_y_cola {q joint success d r : ℝ} (hs : 0 < success)
    (hq : q = joint / success) (hj : joint ≤ Real.exp (-r))
    (survive : Real.exp (-d) ≤ success) :
    q * Real.exp (r-d) ≤ 1 := by
  rw [hq,div_mul_eq_mul_div,div_le_iff₀ hs,one_mul]
  calc
    _ ≤ Real.exp (-r)*Real.exp (r-d) := mul_le_mul_of_nonneg_right hj (Real.exp_pos _).le
    _ = Real.exp (-d) := by rw [←Real.exp_add]; congr 1; ring
    _ ≤ _ := survive

/-- Only the bad probability is transferred. This gives no exponential
concentration rate under the uniform comparison law. -/
theorem transferencia (prob d : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (nn : ∀ᶠ n in atTop, 0 ≤ prob n)
    (small : Tendsto (fun n => d n / (n:ℝ)) atTop (𝓝 0))
    (binaria : ∀ᶠ n : ℕ in atTop, prob n * (c*n - d n) ≤ d n + Real.log 2) :
    Tendsto prob atTop (𝓝 0) := by
  let v := fun n : ℕ => d n / n
  let w := fun n : ℕ => Real.log 2 / n
  have hw := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have denom : Tendsto (fun n => c-v n) atTop (𝓝 c) := by
    simpa [v] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).sub small
  have high : Tendsto (fun n => (v n + w n) / (c-v n)) atTop (𝓝 0) := by
    simpa [v,w] using (small.add hw).div denom hc.ne'
  apply squeeze_zero' nn _ high
  filter_upwards [binaria, (tendsto_order.mp denom).1 0 hc, eventually_gt_atTop (0:ℕ)] with n hn hd hn0
  apply (le_div_iff₀ hd).mpr
  have pos : 0 < (n:ℝ) := by exact_mod_cast hn0
  dsimp [v,w]
  apply (mul_le_mul_iff_of_pos_right pos).mp
  calc
    _ = prob n * (c*n-d n) := by field_simp [pos.ne']
    _ ≤ d n + Real.log 2 := hn
    _ = _ := by field_simp [pos.ne']

end ArticuloA.Entropia
#print axioms ArticuloA.Entropia.exito_y_cola
#print axioms ArticuloA.Entropia.transferencia
