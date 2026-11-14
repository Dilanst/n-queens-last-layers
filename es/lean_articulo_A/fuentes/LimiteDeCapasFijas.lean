import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology
open scoped BigOperators
namespace ArticuloA.Limites

theorem limite_por_doble_cuenta (f I D m : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (identidad : ∀ᶠ n in atTop, f n * I n = m n * D n)
    (hI : Tendsto I atTop (𝓝 b)) (hD : Tendsto D atTop (𝓝 1))
    (hm : Tendsto m atTop (𝓝 1)) :
    Tendsto f atTop (𝓝 (1/b)) := by
  have hq : Tendsto (fun n => (m n * D n) / I n) atTop (𝓝 (1/b)) := by
    simpa only [one_mul] using (hm.mul hD).div hI hb.ne'
  have hpos : ∀ᶠ n in atTop, 0 < I n := (tendsto_order.mp hI).1 0 hb
  apply hq.congr'
  filter_upwards [hpos, identidad] with n ht hi
  exact ((eq_div_iff (ne_of_gt ht)).2 hi).symm

theorem contribucion_fija {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (F : ℝ)
    (hp : 0 < F) (hf : ∀ j ∈ s, Tendsto (f j) atTop (𝓝 F)) :
    Tendsto (fun n => ∑ j ∈ s, Real.log (f j n/F)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∏ j ∈ s, (f j n/F)) atTop (𝓝 1) := by
  classical
  have hratio (j) (hj : j ∈ s) : Tendsto (fun n => f j n / F) atTop (𝓝 1) := by
    simpa [hp.ne'] using (hf j hj).div (tendsto_const_nhds : Tendsto (fun _ : ℕ => F) atTop (𝓝 F)) hp.ne'
  have hlog (j) (hj : j ∈ s) : Tendsto (fun n => Real.log (f j n/F)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp (hratio j hj)
  exact ⟨by simpa using tendsto_finset_sum s hlog, by simpa using tendsto_finset_prod s hratio⟩
/-- The two sampling conventions of §10; j and K stay fixed. -/
theorem extremos_del_perfil (K : ℕ) (f : ℕ → ℕ → ℝ) (F : ℝ → ℝ) (hp : 0 < F 0)
    (cont : ContinuousAt F 0) (layers : ∀ j < K, Tendsto (f (j+1)) atTop (𝓝 (F 0)))
    (s : ℝ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range K,
      Real.log (f (j+1) n / F (((j:ℝ)+1-s)/(n:ℝ)))) atTop (𝓝 0) := by
  have per (j : ℕ) (hj : j ∈ Finset.range K) :
      Tendsto (fun n : ℕ => Real.log (f (j+1) n / F (((j:ℝ)+1-s)/(n:ℝ)))) atTop (𝓝 0) := by
    have prof := cont.tendsto.comp (tendsto_const_div_atTop_nhds_zero_nat ((j:ℝ)+1-s))
    have r := (layers j (Finset.mem_range.mp hj)).div prof hp.ne'
    have r1 : Tendsto (fun n : ℕ => f (j+1) n / F (((j:ℝ)+1-s)/(n:ℝ))) atTop (𝓝 1) := by
      simpa only [Function.comp_apply,div_self hp.ne'] using r
    simpa only [Function.comp_def,Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp r1
  simpa using tendsto_finset_sum (Finset.range K) per
end ArticuloA.Limites
#print axioms ArticuloA.Limites.limite_por_doble_cuenta
#print axioms ArticuloA.Limites.contribucion_fija
