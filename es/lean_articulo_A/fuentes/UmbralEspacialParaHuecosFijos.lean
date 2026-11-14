import PisoDeLaMallaEnCadaCruce
import BandaDelValorDelOptimo
open Filter Set
open scoped NNReal Topology
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 RealFinita
noncomputable section

/-- Uniform over the spatial root. h is fixed before the size tends to infinity. -/
theorem piso_eventual_de_las_raices {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (h : ℕ) (C : ℝ≥0) (balance : ∀ᶠ n : ℕ in atTop,BalanceMalla n h (p ((h:ℝ)/n)) C)
    (y : ℝ) (hy : y<(κ/2)^4) :
    ∀ᶠ n : ℕ in atTop,∀ z : Cell n,y≤(blancoFinalDeMalla h (p ((h:ℝ)/n)) z:ℝ)/n := by
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  let W:ℝ:=4*(M^4/κ^4)
  let c:ℝ:=(κ/2)^4
  have conv : Tendsto (fun n : ℕ => c-(((h:ℝ)+W)*c)/(n:ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x:=c)).sub (tendsto_const_div_atTop_nhds_zero_nat (((h:ℝ)+W)*c))
  obtain ⟨n₀,big⟩:=exists_nat_gt (2*(C:ℝ)/κ)
  filter_upwards [balance,(tendsto_order.mp conv).1 y hy,eventually_ge_atTop n₀,
    eventually_ge_atTop (2*h+2)] with n bal ly ng nn
  intro z
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hh : (h:ℝ)/n∈Icc 0 (1/2:ℝ) := by
    refine ⟨by positivity,(div_le_iff₀ np).mpr ?_⟩
    have cut : 2*(h:ℝ)≤n := by exact_mod_cast (by omega : 2*h≤n)
    linarith
  have mg : 2*(C:ℝ)≤κ*n := by
    have lim : 2*(C:ℝ)/κ≤n := big.le.trans (by exact_mod_cast ng)
    simpa only [mul_comm] using (div_le_iff₀ rama.kp).mp lim
  have floor:=piso_de_la_malla (κ:=lo) (m:=hi) (by omega : 2≤n) (rama.espacio _ hh)
    (show 0<lo from rama.kp) bal mg z
  change ((↑(n-h):ℝ)-W)*c≤_ at floor
  rw [Nat.cast_sub (by omega : h≤n)] at floor
  apply ly.le.trans
  apply (le_div_iff₀ np).mpr
  rw [sub_mul,div_mul_cancel₀ _ np.ne']
  linarith only [floor,show c*(n:ℝ)-((h:ℝ)+W)*c=((n:ℝ)-h-W)*c by ring]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.piso_eventual_de_las_raices
