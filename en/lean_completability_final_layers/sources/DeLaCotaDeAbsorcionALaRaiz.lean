import CotaDeLaRaizPorElTableroVacio
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- Only the first-order lower part is used. -/
theorem raiz_desde_las_tolerancias {s : ℝ} (h : CotaDePrimerOrden s) :
    exp s ≤ liminf (raizDelConteo (fun n=>count n n)) atTop := by
  have sub (ε : ℝ) (ep : 0<ε) :
      exp (s-ε) ≤ liminf (raizDelConteo (fun n=>count n n)) atTop := by
    apply le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop
      (Eventually.of_forall raiz_del_conteo_a_lo_sumo_uno))
    filter_upwards [h ε ep,soluciones_eventuales_del_primer_orden h,eventually_ge_atTop 1]
      with n bound pos hn
    have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
    have qp : 0<(count n n:ℝ):=by exact_mod_cast pos
    have z : s-ε+log n ≤ log (count n n)/(n:ℝ):=by
      apply (le_div_iff₀ np).mpr
      linarith
    change exp (s-ε) ≤ (count n n:ℝ)^((n:ℝ)⁻¹)/(n:ℝ)
    apply (le_div_iff₀ np).mpr
    rw [← Real.exp_log np,← Real.exp_add,Real.exp_log np,Real.rpow_def_of_pos qp]
    exact Real.exp_le_exp.mpr (by simpa [div_eq_mul_inv] using z)
  have lim : Tendsto (fun j : ℕ=>exp (s-1/((j:ℝ)+1))) atTop (𝓝 (exp s)) := by
    simpa [Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=s)).sub tendsto_one_div_add_atTop_nhds_zero_nat)
  exact le_of_tendsto lim (Eventually.of_forall (fun j=>sub _ (by positivity)))

/-- A single rate, for any positive exponent, covers the tolerances. -/
theorem tolerancias_desde_absorcion {s C d : ℝ} (dp : 0<d)
    (abs : ∀ᶠ n : ℕ in atTop,(n:ℝ)*log n+(n:ℝ)*s-C*(n:ℝ)^(1-d)≤log (count n n)) :
    CotaDePrimerOrden s := by
  intro ε ep
  have small : Tendsto (fun n : ℕ=>C*(n:ℝ)^(-d)) atTop (𝓝 0):=by
    simpa using ((tendsto_rpow_neg_atTop dp).comp tendsto_natCast_atTop_atTop).const_mul C
  filter_upwards [abs,small.eventually_lt_const ep,eventually_ge_atTop 1] with n bound cap hn
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  rw [show (1:ℝ)-d=1+(-d) by ring,Real.rpow_add np,Real.rpow_one] at bound
  nlinarith [mul_le_mul_of_nonneg_left cap.le np.le]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.raiz_desde_las_tolerancias
#print axioms ArticuloA.Historias.tolerancias_desde_absorcion
