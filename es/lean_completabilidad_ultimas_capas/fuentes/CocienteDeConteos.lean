import DobleCuentaReal
import RetiradaBinomial
open Filter
open scoped Topology
namespace ArticuloA.Limites
noncomputable section
def conteoEscalado (n h : ℕ) : ℝ :=
  ((count n (n-h):ℝ)*(h.factorial:ℝ)^2)/((count n n:ℝ)*(n:ℝ)^h)

private theorem nivel_positivo (n h : ℕ) (hn : h ≤ n) (q : 0 < count n n) :
    0 < count n (n-h) := by
  by_contra! hz
  have zero := Nat.eq_zero_of_le_zero hz
  have H := Capas.retirada_binomial n h hn
  rw [zero,mul_zero] at H
  exact (Nat.not_le_of_lt (Nat.mul_pos (Nat.choose_pos hn) q)) H

private theorem paso_escalado (n h : ℕ) (inrange : h+1 ≤ n) (full : 0 < count n n) :
    conteoEscalado n (h+1) = conteoEscalado n h *
        ((((n-(h+1)+1:ℕ):ℝ)/n) / fracReal n (h+1)) := by
  have nh : 0 < n := by omega
  have lvl := nivel_positivo n (h+1) inrange full
  have prev := nivel_positivo n h (by omega) full
  have nh' : 0 < n-h := by omega
  have nn : (n:ℝ) ≠ 0 := by exact_mod_cast nh.ne'
  have nq : (count n n:ℝ) ≠ 0 := by exact_mod_cast full.ne'
  have a : (count n (n-(h+1)):ℝ) ≠ 0 := by exact_mod_cast lvl.ne'
  have b : (count n (n-h):ℝ) ≠ 0 := by exact_mod_cast prev.ne'
  have c : ((n-h:ℕ):ℝ) ≠ 0 := by exact_mod_cast nh'.ne'
  have d : (((h+1:ℕ):ℝ)) ≠ 0 := by positivity
  unfold conteoEscalado fracReal
  rw [show n-(h+1)+1=n-h by omega,Nat.factorial_succ,Nat.cast_mul,pow_succ (n:ℝ) h]
  field_simp [nn,nq,a,b,c,d]; ring

/-- Physical counts for a fixed number of holes, with only the layer
limits up to that number assumed. The factorial is squared. -/
theorem limite_conteo (h : ℕ) (F : ℝ) (hp : 0 < F)
    (full : ∀ᶠ n in atTop, 0 < count n n)
    (hf : ∀ j, 1 ≤ j → j ≤ h → Tendsto (fun n => fracReal n j) atTop (𝓝 F)) :
    Tendsto (fun n => conteoEscalado n h) atTop (𝓝 (1/F^h)) := by
  induction h with
  | zero =>
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1/F^0) atTop (𝓝 (1/F^0))).congr'
    filter_upwards [full] with n hn
    have pos : (count n n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [conteoEscalado,pos]
  | succ j ih =>
    have hprev := ih (fun t ht hj => hf t ht (by omega))
    have hstep := (factor_nivel (j+1)).div (hf (j+1) (by omega) (by omega)) hp.ne'
    have comb := hprev.mul hstep
    have eq : 1/F^j*(1/F)=1/F^(j+1) := by rw [pow_succ]; ring
    rw [eq] at comb
    apply comb.congr'
    filter_upwards [full,eventually_ge_atTop (j+1)] with n hn nr
    exact (paso_escalado n j nr hn).symm
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.limite_conteo
