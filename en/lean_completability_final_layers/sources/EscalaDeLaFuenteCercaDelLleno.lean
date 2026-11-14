import ReindexacionDeLasDosEsquinas
import IdentificacionUniformeEnElTableroLleno
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Filter Set
open scoped Topology
theorem error_de_escala_de_las_fuentes {n h : ℕ} {p : FactoresContinuos} {κ M L b : ℝ}
    (hn : 0<n) (sp : ControlEspacial p κ M L) (kp : 0<κ) (mp : 0≤M) (lp : 0≤L) (bp : 0<b)
    (masa : integralTablero (pesoContinuo p)=((↑(n-h):ℝ)/n)/b) :
    |n*escalaDeLasFuentes n h p-b|≤(b*(2*(4*M^3*L))/κ^4)/(n:ℝ) := by
  let U:=Wfisico n p
  let V:=integralTablero (pesoContinuo p)
  let B:=2*(4*M^3*L)
  have nr : 0<(n:ℝ) := by exact_mod_cast hn
  have den : κ^4*(n:ℝ)^2≤U := masa_inferior sp kp.le
  have pos : 0<U := (mul_pos (pow_pos kp 4) (pow_pos nr 2)).trans_le den
  have diff : |n^2*V-U|≤B*n := by rw [abs_sub_comm]; exact cuadratura_total_fisica hn sp mp lp
  have eq : n*escalaDeLasFuentes n h p-b=b*(n^2*V-U)/U := by
    unfold escalaDeLasFuentes; dsimp [U,V]; rw [masa]; field_simp; ring
  rw [eq,abs_div,abs_mul,abs_of_pos bp,abs_of_pos pos]
  apply (div_le_div₀ (by dsimp [B]; positivity) (mul_le_mul_of_nonneg_left diff bp.le)
    (mul_pos (pow_pos kp 4) (pow_pos nr 2)) den).trans_eq
  dsimp [B]; field_simp; ring

theorem escala_de_las_fuentes_al_lleno {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (h : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)*escalaDeLasFuentes n h (p ((h:ℝ)/n))) atTop (𝓝 (b 0)) := by
  let x:=fun n : ℕ => (h:ℝ)/n
  have x0:=tendsto_const_div_atTop_nhds_zero_nat (h:ℝ)
  have domain : ∀ᶠ n : ℕ in atTop,x n∈Icc 0 (1/2:ℝ) := by
    filter_upwards [(tendsto_order.mp x0).2 (1/2) (by norm_num)] with n small
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),small.le⟩
  have bc : Tendsto (fun n => b (x n)) atTop (𝓝 (b 0)) := by
    apply Metric.tendsto_nhds.mpr
    intro η ep
    obtain ⟨d,dp,cl⟩:=cont (η/2) (half_pos ep)
    filter_upwards [domain,(tendsto_order.mp x0).2 d dp] with n nx near
    exact ((cl _ nx near).1.trans_lt (half_lt_self ep) : |b (x n)-b 0|<η)
  have err : Tendsto (fun n : ℕ => (n:ℝ)*escalaDeLasFuentes n h (p (x n))-b (x n)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η ep
    let D:=B*(2*(4*M^3*L))/κ^4
    filter_upwards [domain,(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat D)).2 η ep,
      eventually_ge_atTop h,eventually_gt_atTop 0] with n hx small nh np
    have E:=rama.euler (x n) hx
    have mass:=integral_masa_cuadrada E
    rw [E.masa,Real.coe_toNNReal _ hx.1] at mass
    have scale : 1-x n=(↑(n-h):ℝ)/n := by rw [Nat.cast_sub nh]; dsimp [x]; field_simp
    rw [scale] at mass
    have bound:=error_de_escala_de_las_fuentes np (rama.espacio (x n) hx) rama.kp (zero_le_one.trans rama.m1)
      rama.lp E.coef mass
    rw [Real.dist_eq,sub_zero]
    have mp : 0≤M := zero_le_one.trans rama.m1
    have lp := rama.lp
    exact bound.trans_lt (lt_of_le_of_lt (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (rama.cota _ hx) (by positivity)) (pow_nonneg rama.kp.le 4))
      (Nat.cast_nonneg n)) small)
  simpa only [sub_add_cancel,zero_add] using err.add bc
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_escala_de_las_fuentes
#print axioms ArticuloA.Historias.escala_de_las_fuentes_al_lleno
