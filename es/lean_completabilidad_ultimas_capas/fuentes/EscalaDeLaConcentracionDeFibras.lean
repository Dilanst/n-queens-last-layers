import ConcentracionSimultaneaDeLasCuatroFamilias
import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open Repair Limites Real Filter
open scoped Topology BigOperators
noncomputable section
open Classical

theorem fibras_con_peso_sobre_n_tienen_fallo_a_lo_sumo_n_menos_cuatro (A : ℝ) (ap : 0<A) :
    ∀ᶠ n : ℕ in atTop, ∀ (w : Cell n→ℝ) (τ : ℝ), τ∈Set.Icc (0:ℝ) 1 →
      (∀ e,|w e|≤A/n) →
      mediaCubo τ (fun u=>if ∃ i : FibraDeB1 n,(n:ℝ)^(-(1/4:ℝ))≤
        |masaAuxiliar w i u-centroDeLaFibra τ w i| then 1 else 0) ≤ 1/(n:ℝ)^4 := by
  have rate : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^(1/2:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have small : Tendsto (fun n : ℕ=>(n:ℝ)^(-(1/4:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  have cp : 0<1/(168*A^2) := by positivity
  filter_upwards [eventually_ge_atTop 4,rate.eventually_lt_const cp,
    small.eventually_lt_const (show 0<8*A by linarith)] with n n4 rate' tSmall
  intro w τ prob cap
  have nr : 4≤(n:ℝ):=by exact_mod_cast n4
  have np : 0<(n:ℝ):=by linarith
  let t:=(n:ℝ)^(-(1/4:ℝ))
  have tp : 0<t:=Real.rpow_pos_of_pos np _
  have bp : 0<A/(n:ℝ):=div_pos ap np
  have cut : t≤2*(4*(n:ℝ)+2)*(A/n) := by
    dsimp [t]
    apply tSmall.le.trans
    rw [←mul_div_assoc,le_div_iff₀ np]
    nlinarith only [ap]
  have h:=cola_simultanea_de_todas_las_fibras w (A/n) τ t prob bp cap tp.le cut
  have power : t^2*(n:ℝ)=(n:ℝ)^(1/2:ℝ) := by
    dsimp [t]
    rw [←Real.rpow_mul_natCast np.le,←Real.rpow_add_one np.ne']
    norm_num
  have Dpos : 0<4*(4*(n:ℝ)+2)*(A/n)^2 := by positivity
  have denom : (4*(4*(n:ℝ)+2)*(A/n)^2)*(n:ℝ) ≤ 24*A^2 := by
    calc
      _ = 4*(4*(n:ℝ)+2)*A^2/n := by field_simp [np.ne']; ring
      _ ≤ 24*A^2 := by
        rw [div_le_iff₀ np]
        nlinarith only [mul_nonneg (sq_nonneg A) (show 0≤(n:ℝ)-1 by linarith)]
  have rate2:=(div_lt_iff₀ (Real.rpow_pos_of_pos np (1/2:ℝ))).mp rate'
  have logpos : 0≤log (n:ℝ):=Real.log_nonneg (by linarith)
  have limit : 7*log (n:ℝ)*(24*A^2) ≤ t^2*(n:ℝ) := by
    rw [power]
    have r : log (n:ℝ)<(n:ℝ)^(1/2:ℝ)/(168*A^2) := by simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using rate2
    have rr:=(lt_div_iff₀ (by positivity : 0<168*A^2)).mp r
    linarith only [rr]
  have prod:=mul_le_mul_of_nonneg_left denom (show 0≤7*log (n:ℝ) by linarith)
  have et : -(t^2)/(4*(4*(n:ℝ)+2)*(A/n)^2) ≤ -(7*log n) := by
    rw [div_le_iff₀ Dpos]
    apply le_of_mul_le_mul_right _ np
    linarith only [prod,limit]
  have eq : exp (-(7*log (n:ℝ)))=1/(n:ℝ)^7 := by
    rw [Real.exp_neg,show (7:ℝ)*log n=((7:ℕ):ℝ)*log n by norm_num,Real.exp_nat_mul,Real.exp_log np,one_div]
  have poly : 2*(6*(n:ℝ)+2)≤(n:ℝ)^3 := by
    nlinarith only [nr,mul_nonneg np.le (show 0≤((n:ℝ)-4)*((n:ℝ)+4) from mul_nonneg (sub_nonneg.mpr nr) (by positivity)), nr]
  apply h.trans
  calc
    _ ≤ (6*(n:ℝ)+2)*(2*exp (-(7*log n))) := by gcongr
    _ ≤ _ := by
      rw [eq]
      calc
        _ = (2*(6*(n:ℝ)+2))/(n:ℝ)^7 := by ring
        _ ≤ (n:ℝ)^3/(n:ℝ)^7 := div_le_div_of_nonneg_right poly (by positivity)
        _ = _ := by field_simp [np.ne']; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.fibras_con_peso_sobre_n_tienen_fallo_a_lo_sumo_n_menos_cuatro
