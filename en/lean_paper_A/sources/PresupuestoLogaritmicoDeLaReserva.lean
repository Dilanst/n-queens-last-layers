import HolguraAlRitmoDeLosHuecosDeReserva
namespace ArticuloA.Historias
open Filter Real
open scoped Topology
noncomputable section

theorem escalas_del_costo_entropico (s : ℝ) (sp : 0<s) :
    ∀ᶠ n : ℕ in atTop,
      let ε:=fraccionReserva n
      let τ:=(n:ℝ)^(-exponenteReserva)
      let l:=log (1/ε)
      0<ε ∧ 1≤l ∧ (n:ℝ)^(-(1/4:ℝ))≤τ ∧ 1≤τ*n ∧
        log (n:ℝ)≤l/(4*exponenteReserva) ∧ |log (s*ε/4)|≤(|log (s/4)|+1)*l := by
  have αp : 0<exponenteReserva := by norm_num [exponenteReserva]
  have growing : Tendsto (fun n : ℕ=>log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,cortes_de_la_reserva,
    growing.eventually_ge_atTop (1/(4*exponenteReserva))] with n n1 cuts big
  dsimp only
  have nr : 1≤(n:ℝ) := by exact_mod_cast n1
  have np : 0<(n:ℝ) := by linarith
  have m1 : (1:ℝ)≤(huecosReserva n:ℝ) := by exact_mod_cast cuts.1
  let ε:=fraccionReserva n
  have ep : 0<ε := by
    change 0<(huecosReserva n:ℝ)/(n:ℝ)
    exact div_pos (by linarith) np
  have rp := Real.rpow_pos_of_pos np (4*exponenteReserva)
  have le : (n:ℝ)^(4*exponenteReserva)≤1/ε := by
    rw [le_div_iff₀ ep]
    have upper:=(le_div_iff₀ rp).mp cuts.2.2.2
    change ε*(n:ℝ)^(4*exponenteReserva)≤1/8000 at upper
    linarith only [upper]
  have coef : 0<4*exponenteReserva := by positivity
  have logarithm:=Real.log_le_log rp le
  rw [Real.log_rpow np] at logarithm
  have big':=(div_le_iff₀ coef).mp big
  have lo : 1≤log (1/ε) := by linarith only [big',logarithm]
  have loge : |log ε|=log (1/ε) := by
    rw [one_div,Real.log_inv]
    apply abs_of_nonpos
    rw [one_div,Real.log_inv] at lo
    linarith
  have split : log (s*ε/4)=log (s/4)+log ε := by
    rw [←Real.log_mul (by positivity : (s/4:ℝ)≠0) ep.ne']; congr 1; ring
  refine ⟨ep,lo,Real.rpow_le_rpow_of_exponent_le nr (by norm_num [exponenteReserva]),?_,?_,?_⟩
  · rw [←Real.rpow_add_one np.ne']
    apply Real.one_le_rpow nr
    norm_num [exponenteReserva]
  · apply (le_div_iff₀ coef).mpr
    linarith only [logarithm]
  · change |log (s*ε/4)|≤_
    rw [split]
    apply (abs_add_le _ _).trans
    rw [loge]
    have p:=mul_le_mul_of_nonneg_left lo (abs_nonneg (log (s/4)))
    linarith only [p]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.escalas_del_costo_entropico
