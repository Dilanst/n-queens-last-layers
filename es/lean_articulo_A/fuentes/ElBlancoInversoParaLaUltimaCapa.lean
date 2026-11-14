import LaMediaExteriorEnElPesoDeReparacion
import EscalaDeLaFuenteCercaDelLleno
import EulerPuntualEnLasCuatroFamilias
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Filter Set
open scoped Topology
theorem media_exterior_del_peso_inverso {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) :
    Tendsto (fun n : ℕ => mediaExterior (fun z : Cell n =>
      (1/aDelLleno p b z)*productoRCEnElCentro (p ((j:ℝ)/n)) z*
        perfilDirectoSinFiltro j (p ((j:ℝ)/n)) z)) atTop (𝓝 1) := by
  let x:=fun n : ℕ => (j:ℝ)/n
  let U:=fun (n : ℕ) (z : Cell n) => productoRCEnElCentro (p (x n)) z
  let F:=fun (n : ℕ) (z : Cell n) => (1/aDelLleno p b z)*U n z*perfilDirectoSinFiltro j (p (x n)) z
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bp:=(rama.euler 0 zero).coef
  let m:=b 0*κ^8
  have mp : 0<m := mul_pos bp (pow_pos rama.kp _)
  have err : Tendsto (fun n => mediaExterior (F n)-mediaExterior (U n)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    let d:=ε/2/(M^2/m+1)
    have dp : 0<d := div_pos (half_pos ep) (by positivity)
    filter_upwards [sin_filtro_converge_al_perfil_directo rama cont j d dp,
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (1/2) (by norm_num)] with n close nx
    rw [Real.dist_eq,sub_zero]
    have sp:=rama.espacio (x n) ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),nx.le⟩
    apply lt_of_le_of_lt (continuidad_de_la_media_exterior (F n) (U n) (ε/2) (half_pos ep).le _) (half_lt_self ep)
    intro z
    have hr:=medio_admisible z.1.isLt
    have hc:=medio_admisible z.2.isLt
    have minA : m≤aDelLleno p b z := piso_integral_del_cruce (rama.espacio 0 zero) rama.kp rama.lp bp hr hc
    have Apos:=mp.trans_le minA
    have ucap : |U n z|≤M^2 := by
      change |(_ : ℝ)*_|≤M^2
      rw [abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)),pow_two]
      exact mul_le_mul (sp.Rmax _ hr) (sp.Cmax _ hc) (NNReal.coe_nonneg _) (zero_le_one.trans rama.m1)
    have id : F n z-U n z=(perfilDirectoSinFiltro j (p (x n)) z-aDelLleno p b z)*(U n z/aDelLleno p b z) := by
      dsimp only [F]; field_simp [Apos.ne']; ring
    rw [id,abs_mul,abs_div,abs_of_pos Apos]
    have bound:=mul_le_mul (close z) (div_le_div₀ (sq_nonneg M) ucap mp minA)
      (div_nonneg (abs_nonneg _) Apos.le) dp.le
    apply bound.trans
    calc d*(M^2/m) ≤ d*(M^2/m+1) := mul_le_mul_of_nonneg_left (by linarith) dp.le
         _ = ε/2 := by unfold d; exact div_mul_cancel₀ _ (show M^2/m+1≠0 by positivity)
  have rc : Tendsto (fun n => mediaExterior (U n)) atTop (𝓝 1) := media_RC_tiende_a_uno rama j
  simpa only [sub_add_cancel,zero_add] using err.add rc

theorem centro_discreto_inverso_tiende_a_b {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) :
    Tendsto (fun n : ℕ => blancoInverso (n:=n) j (p ((j:ℝ)/n)) (fun z => 1/aDelLleno p b z) 1/(n:ℝ)^2)
      atTop (𝓝 (b 0)) := by
  let x:=fun n : ℕ => (j:ℝ)/n
  let w:=fun (n : ℕ) (z : Cell n) => 1/aDelLleno p b z
  let main:=fun n : ℕ => (n*escalaDeLasFuentes n j (p (x n)))*
    mediaExterior (fun z => w n z*productoRCEnElCentro (p (x n)) z*perfilDirectoSinFiltro j (p (x n)) z)
  have mainLimit : Tendsto main atTop (𝓝 (b 0)) := by
    simpa only [mul_one] using (escala_de_las_fuentes_al_lleno rama cont j).mul (media_exterior_del_peso_inverso rama cont j)
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  let W:=1/(b 0*κ^8)
  have bp:=(rama.euler 0 zero).coef
  have floor : 0<b 0*κ^8 := mul_pos bp (pow_pos rama.kp _)
  have wp : 0≤W := div_nonneg zero_le_one floor.le
  have cap (n) (z : Cell n) : |w n z|≤W := by
    have a:=piso_integral_del_cruce (rama.espacio 0 zero) rama.kp rama.lp bp (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
    change b 0*κ^8≤aDelLleno p b z at a
    change |1/aDelLleno p b z|≤W
    rw [abs_of_nonneg (div_nonneg zero_le_one (floor.le.trans a))]
    exact div_le_div_of_nonneg_left zero_le_one floor a
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama (euler_puntual_de_la_rama rama)
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  let D:=4*W*(M^4/κ^4)^2+W*(1+M)*C
  have negligible : Tendsto (fun n : ℕ => blancoInverso j (p (x n)) (w n) 1/(n:ℝ)^2-main n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [bal j,(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat D)).2 ε ep,
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (1/2) (by norm_num),
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (2*(C:ℝ)))).2 κ rama.kp,
      eventually_ge_atTop 2] with n balance small den mar nn
    have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have sp:=rama.espacio (x n) ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),den.le⟩
    rw [Real.dist_eq,sub_zero]
    exact (reduccion_a_la_media_exterior (κ:=lo) (m:=hi) nn sp (show 0<lo from rama.kp) balance
      ((div_le_iff₀ nr).mp mar.le) (w n) wp (cap n)).trans_lt small
  simpa only [sub_add_cancel,zero_add] using negligible.add mainLimit
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_exterior_del_peso_inverso
#print axioms ArticuloA.Historias.centro_discreto_inverso_tiende_a_b
