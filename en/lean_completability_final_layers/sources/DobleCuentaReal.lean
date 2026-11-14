import LimiteDeCapasFijas
import PositividadDesdeCruces
import Mathlib.Analysis.SpecificLimits.Basic
open Filter
open scoped Topology
namespace ArticuloA.Limites
noncomputable section
theorem factor_nivel (h : ℕ) :
    Tendsto (fun n : ℕ => ((n-h+1:ℕ):ℝ)/n) atTop (𝓝 1) := by
  have cv := tendsto_const_div_atTop_nhds_zero_nat (1-(h:ℝ))
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add cv
  apply (show Tendsto (fun n : ℕ => 1 + (1-(h:ℝ))/(n:ℝ)) atTop (𝓝 1) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop h, eventually_gt_atTop (0:ℕ)] with n nh nn
  rw [Nat.cast_add,Nat.cast_sub nh,Nat.cast_one]
  have pos : (n:ℝ) ≠ 0 := by exact_mod_cast nn.ne'
  field_simp [pos]; ring

theorem limite_fisico (h : ℕ) (hh : h ≠ 0) (w : (n : ℕ) → Cell n → ℝ) {b : ℝ} (hb : 0 < b)
    (niveles : ∀ᶠ n in atTop, count n (n-h) ≠ 0 ∧ count n (n-h+1) ≠ 0)
    (hd : Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 1))
    (hi : Tendsto (fun n => mediaI n h (w n)) atTop (𝓝 b))
    :
    Tendsto (fun n => fracReal n h) atTop (𝓝 (1/b)) := by
  apply limite_por_doble_cuenta _ _ _ _ _ hb _ hi hd (factor_nivel h)
  filter_upwards [niveles, eventually_gt_atTop (0:ℕ)] with n hn hpos
  exact relacion_fisica _ hpos.ne' hh hn.1 hn.2
/-- Lower bound at fixed h. A typical per-cross guarantee leaves the
same constant a after normalisation by all h² holes. -/
theorem positividad_tipica (h : ℕ) (hh : 0<h) (a : ℝ) (ha : 0<a)
    (G : (n : ℕ) → Placement n → Prop)
    (nonempty : ∀ᶠ n in atTop, 0 < count n (n-h))
    (many : ∀ᶠ n in atTop, ∀ p : Placement n, Legal p → pieces p = n-h → G n p →
      ∀ z, Repair.emptyCross p z → a*n ≤ (Repair.crossDegree (n-h) p z:ℝ))
    (typical : Tendsto (fun n => probBuena n h (G n)) atTop (𝓝 1)) :
    ∀ a' < a, ∀ᶠ n in atTop, a' < fracReal n h := by
  have cv : Tendsto (fun n => a*probBuena n h (G n)) atTop (𝓝 a) := by
    simpa only [mul_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).mul typical
  intro a' ha'
  filter_upwards [(tendsto_order.mp cv).1 a' ha', eventually_gt_atTop h,nonempty,many] with n hl nr nz hg
  have qpos : 0<n-h := by omega
  have qp : 0<((n-h:ℕ):ℝ) := by exact_mod_cast qpos
  have le : ((n-h:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n h
  have lift : a ≤ a*n/((n-h:ℕ):ℝ) := (le_div_iff₀ qp).mpr (mul_le_mul_of_nonneg_left le ha.le)
  have pr : 0 ≤ probBuena n h (G n) := by unfold probBuena; positivity
  exact hl.trans_le ((mul_le_mul_of_nonneg_right lift pr).trans (desde_cruces n h hh qpos nz a (G n) hg))
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.relacion_fisica
#print axioms ArticuloA.Limites.limite_fisico
#print axioms ArticuloA.Limites.positividad_tipica
