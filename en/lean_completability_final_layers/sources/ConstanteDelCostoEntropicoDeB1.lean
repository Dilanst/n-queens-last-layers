import PresupuestoLogaritmicoDeLaReserva
namespace ArticuloA.Historias
open Filter Real
open scoped Topology

noncomputable def constanteB1 (s : ℝ) : ℝ := 3*(2/(4*exponenteReserva)+2+8*(2+|log (s/4)|))+1

theorem perdida_en_presupuesto_N3A2_7 (s : ℝ) (sp : 0<s) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0≤D →
      let τ:=(n:ℝ)^(-exponenteReserva)
      let t:=(n:ℝ)^(-(1/4:ℝ))
      let ε:=fraccionReserva n
      D≤(2*τ+t)*n →
      D*(2*log n+2+8*(1+|log (s*ε/4)|))+1 ≤ constanteB1 s*τ*n*log (1/ε) := by
  filter_upwards [escalas_del_costo_entropico s sp,eventually_ge_atTop 1] with n scales n1
  intro D nd
  dsimp only
  intro cap
  let τ:=(n:ℝ)^(-exponenteReserva)
  let l:=log (1/fraccionReserva n)
  let C:=2/(4*exponenteReserva)+2+8*(2+|log (s/4)|)
  obtain ⟨_,large,sm,prod,lg,abslog⟩:=scales
  have coef : 0<4*exponenteReserva := by norm_num [exponenteReserva]
  have nn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have τn : 0≤τ*(n:ℝ) := mul_nonneg (Real.rpow_nonneg nn _) nn
  have lp : 0≤l := by change 1≤l at large; linarith only [large]
  change log (n:ℝ)≤l/(4*exponenteReserva) at lg
  change |log (s*fraccionReserva n/4)|≤(|log (s/4)|+1)*l at abslog
  have rc : 2*log n+2+8*(1+|log (s*fraccionReserva n/4)|)≤C*l := by
    have e : (2/(4*exponenteReserva))*l=2*(l/(4*exponenteReserva)) := by ring
    dsimp [C]
    linarith only [large,lg,abslog,e]
  have dc : D≤3*(τ*n) := by
    change D≤(2*τ+_)*(n:ℝ) at cap
    have a:=mul_le_mul_of_nonneg_right sm nn
    linarith only [cap,a]
  have cl : 0≤C*l := by dsimp [C]; positivity
  have bound := (mul_le_mul_of_nonneg_left rc nd).trans (mul_le_mul_of_nonneg_right dc cl)
  have plus : 1≤(τ*n)*l := by
    change 1≤τ*(n:ℝ) at prod
    exact (by norm_num : (1:ℝ)≤1*1).trans (mul_le_mul prod large (by norm_num) τn)
  change _ ≤ constanteB1 s*τ*n*l
  change _ ≤ (3*C+1)*τ*n*l
  linarith only [bound,plus]

end ArticuloA.Historias
#print axioms ArticuloA.Historias.perdida_en_presupuesto_N3A2_7
