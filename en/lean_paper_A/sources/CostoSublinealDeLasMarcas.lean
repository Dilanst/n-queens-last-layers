import DeLaCotaDeAbsorcionALaRaiz
import MultiplicidadPorLasMarcasDelIntercambio
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- In particular, this includes m=floor(κ n^(1−4/146)). -/
theorem costo_de_marcas_es_sublineal {m : ℕ→ℕ} {C d : ℝ} (dp : 0<d)
    (bound : ∀ᶠ n : ℕ in atTop,(m n:ℝ)≤C*(n:ℝ)^(1-d)) :
    Tendsto (fun n : ℕ=>4*(m n:ℝ)*log n/(n:ℝ)) atTop (𝓝 0) := by
  have decay : Tendsto (fun n : ℕ=>Real.log (n:ℝ)/(n:ℝ)^d) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop dp).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have upper : Tendsto (fun n : ℕ=>(4*C)*(log (n:ℝ)/(n:ℝ)^d)) atTop (𝓝 0):=by
    simpa using decay.const_mul (4*C)
  refine squeeze_zero_norm' ?_ upper
  filter_upwards [bound,eventually_ge_atTop 1] with n hm hn
  have one : (1:ℝ)≤n:=by exact_mod_cast hn
  have np : 0<(n:ℝ):=by linarith
  have lp:=Real.log_nonneg one
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.rpow_sub np,Real.rpow_one] at hm
  have powp:=Real.rpow_pos_of_pos np d
  calc
    _ ≤ 4*(C*((n:ℝ)/(n:ℝ)^d))*log n/n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤4)) lp) np.le
    _ = _ := by field_simp; ring

theorem primer_orden_de_las_salidas_completables {s : ℝ} (m : ℕ→ℕ)
    (O : (n : ℕ)→Finset (Placement n)) (r : ℕ→ℝ)
    (rr : Tendsto (fun n : ℕ=>r n/(n:ℝ)) atTop (𝓝 0))
    (cost : Tendsto (fun n : ℕ=>4*(m n:ℝ)*log n/(n:ℝ)) atTop (𝓝 0))
    (salidas : ∀ᶠ n : ℕ in atTop,(O n).Nonempty ∧
      (n:ℝ)*log n+(n:ℝ)*s-r n≤log ((O n).card:ℝ) ∧
      ∀ p∈O n,∃ ms : Fin (m n)→Mark n,aplicarMarcas (List.ofFn ms) p∈nivel n n) :
    CotaDePrimerOrden s := by
  intro ε ep
  have loss : Tendsto (fun n : ℕ=>r n/(n:ℝ)+4*(m n:ℝ)*log n/(n:ℝ)) atTop (𝓝 0):=by
    simpa using rr.add cost
  filter_upwards [loss.eventually_lt_const ep,salidas,eventually_ge_atTop 1] with n sm h hn
  obtain ⟨ne,ent,paths⟩:=h
  have cap:=cardinal_de_los_parciales_completables (O n) paths
  have op : (0:ℝ)<(O n).card:=by exact_mod_cast Finset.card_pos.mpr ne
  have cp : 0<count n n:=by
    have opos:=Finset.card_pos.mpr ne
    by_contra! z
    rw [Nat.eq_zero_of_le_zero z,zero_mul] at cap
    omega
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have upper:=Real.log_le_log op (show ((O n).card:ℝ)≤(count n n:ℝ)*(n:ℝ)^(4*m n) by exact_mod_cast cap)
  rw [Real.log_mul (by exact_mod_cast cp.ne') (pow_ne_zero _ np.ne'),Real.log_pow] at upper
  push_cast at upper
  rw [←add_div] at sm
  have total:=(div_lt_iff₀ np).mp sm
  linarith

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.costo_de_marcas_es_sublineal
#print axioms ArticuloA.Historias.primer_orden_de_las_salidas_completables
