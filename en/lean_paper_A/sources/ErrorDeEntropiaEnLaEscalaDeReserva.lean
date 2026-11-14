import EscalaDeReservaDeN3A2
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- Error of the entropy bound, divided by n. -/
def errorDeLaReserva (n : ℕ) := (1/fraccionReserva n)^18*(log (n:ℝ))^2/Real.sqrt n+
  (n:ℝ)^(-exponenteReserva)*log (1/fraccionReserva n)

theorem error_de_reserva_tiende_a_cero : Tendsto errorDeLaReserva atTop (𝓝 0) := by
  let a:=exponenteReserva
  have ap : 0<a:=by norm_num [a,exponenteReserva]
  have log2 : Tendsto (fun n : ℕ=>(log (n:ℝ))^2/(n:ℝ)^a) atTop (𝓝 0):=by
    simpa using ((isLittleO_log_rpow_rpow_atTop (2:ℝ) ap).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop)
  have log1 : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^a) atTop (𝓝 0):=
    (isLittleO_log_rpow_atTop ap).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have top : Tendsto (fun n : ℕ=>(16000:ℝ)^18*((log (n:ℝ))^2/(n:ℝ)^a)+log (n:ℝ)/(n:ℝ)^a)
    atTop (𝓝 0):=by simpa using (log2.const_mul ((16000:ℝ)^18)).add log1
  refine squeeze_zero_norm' ?_ top
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1] with n cut hn
  have one : (1:ℝ)≤n:=by exact_mod_cast hn
  have np : 0<(n:ℝ):=by linarith
  have dp:=Real.rpow_pos_of_pos np (4*a)
  have mone : (1:ℝ)≤huecosReserva n:=by exact_mod_cast cut.1
  have mn : (huecosReserva n:ℝ)≤n:=by exact_mod_cast cut.2.1
  have ep : 0<fraccionReserva n:=div_pos (by linarith) np
  have e1 : fraccionReserva n≤1:=(div_le_one np).mpr mn
  have low : 1≤1/fraccionReserva n:=(one_le_div ep).mpr e1
  have invn : 1/fraccionReserva n≤n:=by
    apply (div_le_iff₀ ep).mpr
    change 1≤(n:ℝ)*((huecosReserva n:ℝ)/n)
    convert mone using 1
    field_simp
  have invp : 1/fraccionReserva n≤16000*(n:ℝ)^(4*a):=by
    apply (div_le_iff₀ ep).mpr
    have l:=(div_le_iff₀ dp).mp cut.2.2.1
    nlinarith only [l]
  have p18:=pow_le_pow_left₀ (one_div_nonneg.mpr ep.le) invp 18
  rw [mul_pow,←Real.rpow_mul_natCast np.le] at p18
  have equality : (n:ℝ)^(4*a*(18:ℕ))/Real.sqrt n=1/(n:ℝ)^a:=by
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub np,show 4*a*(18:ℕ)-(1/(2:ℝ))= -a by norm_num [a,exponenteReserva],
      Real.rpow_neg np.le,one_div]
  have first:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right p18 (sq_nonneg (log (n:ℝ)))) (Real.sqrt_nonneg (n:ℝ))
  have first' : (1/fraccionReserva n)^18*(log (n:ℝ))^2/Real.sqrt n≤
      (16000:ℝ)^18*((log (n:ℝ))^2/(n:ℝ)^a):=by
    calc
      _ ≤ _ := first
      _ = (16000:ℝ)^18*(log (n:ℝ))^2*((n:ℝ)^(4*a*(18:ℕ))/Real.sqrt n) := by ring
      _ = _ := by rw [equality]; ring
  have l0:=Real.log_nonneg low
  have l1:=Real.log_le_log (one_div_pos.mpr ep) invn
  have last:=mul_le_mul_of_nonneg_left l1 (Real.rpow_nonneg np.le (-a))
  unfold errorDeLaReserva
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  rw [Real.rpow_neg np.le,←div_eq_inv_mul] at last
  change _ + (n:ℝ)^(-a)*log (1/fraccionReserva n)≤_
  rw [Real.rpow_neg np.le,←div_eq_inv_mul]
  apply add_le_add first'
  simpa only [div_eq_inv_mul] using last

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_reserva_tiende_a_cero
