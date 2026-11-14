import NormalizadorDeLaPiezaMarcada
import RetiradaLogaritmica
import TransferenciaAsintotica
open Filter
open scoped Topology BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section

def ultimoRango (n : ℕ) := if hn : 2≤n then corteFisico n hn else 0

theorem cubo_del_corte (n : ℕ) (hn : 2≤n) :
    (((ultimoRango n-1:ℕ):ℝ))^3 ≤ 4*(n:ℝ)^2 := by
  rw [ultimoRango,dif_pos hn]
  have c := (Rangos.corte_inferior (2*n-1-1) (by omega)).2.2
  have lin : 2*n-1-1 ≤ 2*n := by omega
  have upper := c.le.trans (Nat.pow_le_pow_left lin 2)
  change (↑(Rangos.corte (2*n-1-1) (by omega)-1):ℝ)^3≤_
  have main : (↑(Rangos.corte (2*n-1-1) (by omega)-1):ℝ)^3≤(2*(n:ℝ))^2 := by exact_mod_cast upper
  nlinarith only [main]

theorem corte_es_sublineal :
    Tendsto (fun n => (ultimoRango n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have prev : Tendsto (fun n => (↑(ultimoRango n-1):ℝ)/(n:ℝ)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr; intro ε eps
    have high := (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ))).2 (ε^3) (pow_pos eps 3)
    filter_upwards [eventually_ge_atTop 2,high] with n hn h
    have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
    by_contra! large
    have pow := pow_le_pow_left₀ eps.le large 3
    have rhs : ((↑(ultimoRango n-1):ℝ)/(n:ℝ))^3≤4/(n:ℝ) := by
      rw [div_pow]; apply (div_le_iff₀ (pow_pos np 3)).mpr
      calc
        _ ≤ _ := cubo_del_corte n hn
        _ = _ := by field_simp; ring
    exact (not_lt_of_ge (pow.trans rhs)) h
  have plus := prev.add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  rw [add_zero] at plus
  apply plus.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have kp : 1≤ultimoRango n := by
    rw [ultimoRango,dif_pos hn]; exact (Rangos.corte_inferior _ _).1
  rw [←add_div,Nat.cast_sub kp,Nat.cast_one,sub_add_cancel]

theorem resto_es_sublineal (A : ℝ) :
    Tendsto (fun n : ℕ => (4+(4+60*A)*(ultimoRango n:ℝ))/(n:ℝ)) atTop (𝓝 0) := by
  have main := (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ)).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 4+60*A) atTop (𝓝 (4+60*A))).mul corte_es_sublineal)
  simpa only [mul_zero,zero_add,add_div,mul_div_assoc] using main

theorem log_factorial_inferior (k : ℕ) : (k:ℝ)*Real.log k-k ≤ Real.log k.factorial := by
  cases k with
  | zero => simp
  | succ k =>
    have kp : (0:ℝ)<(k+1:ℕ) := by positivity
    have f := Real.pow_div_factorial_le_exp _ kp.le (k+1)
    have hb := Real.log_le_log (div_pos (pow_pos kp _) (by positivity)) f
    rw [Real.log_div (pow_ne_zero _ kp.ne') (by positivity),Real.log_pow,Real.log_exp] at hb
    linarith
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.corte_es_sublineal
#print axioms ArticuloA.Historias.log_factorial_inferior
