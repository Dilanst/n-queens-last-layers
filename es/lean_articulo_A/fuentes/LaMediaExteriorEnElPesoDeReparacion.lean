import MediaExteriorDeLaInversa
import ConsecuenciasDesdeElPerfilYElConteoLocal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Filter Set
open scoped Topology Interval
private theorem media_de_una_transversal (f : ℕ→ℝ→ℝ≥0) (κ L : ℝ) (lp : 0≤L)
    (data : ∀ᶠ n : ℕ in atTop,RegularEn unidadCerrada (f n) κ L ∧ (∫ t in (0:ℝ)..1,(f n t:ℝ))=1) :
    Tendsto (fun n : ℕ => (∑ i : Fin n,(f n (medio n i.val):ℝ))/n) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  filter_upwards [data,(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat L)).2 ε ep,
    eventually_gt_atTop 0] with n ok small np
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  obtain ⟨reg,mass⟩:=ok
  have s:=cuadratura_centros n np (fun t => (f n t:ℝ)) L lp (continua_de_cota lp reg.oscilacion) reg.oscilacion
  rw [mass,mul_one,abs_sub_comm,Finset.sum_range] at s
  have r : |(∑ i : Fin n,(f n (medio n i.val):ℝ))-(n:ℝ)|≤L := by
    simpa only [centro,nodo,zero_add,medio] using s
  rw [Real.dist_eq,show (∑ i : Fin n,(f n (medio n i.val):ℝ))/n-1=
    ((∑ i : Fin n,(f n (medio n i.val):ℝ))-n)/n by field_simp,abs_div,abs_of_pos nr]
  exact (div_le_div_of_nonneg_right r nr.le).trans_lt small

theorem media_RC_tiende_a_uno {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (j : ℕ) :
    Tendsto (fun n : ℕ => mediaExterior (productoRCEnElCentro (n:=n) (p ((j:ℝ)/n)))) atTop (𝓝 1) := by
  let x:=fun n : ℕ => (j:ℝ)/n
  have domain : ∀ᶠ n : ℕ in atTop,x n∈Icc (0:ℝ) (1/2:ℝ) := by
    filter_upwards [(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (1/2) (by norm_num)] with n small
    exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),small.le⟩
  have row:=media_de_una_transversal (fun n => (p (x n)).fila) κ L rama.lp
    (domain.mono (fun n hx => ⟨(rama.espacio _ hx).R,(rama.normaliza _ hx).1⟩))
  have col:=media_de_una_transversal (fun n => (p (x n)).columna) κ L rama.lp
    (domain.mono (fun n hx => ⟨(rama.espacio _ hx).C,(rama.normaliza _ hx).2⟩))
  simp_rw [media_del_producto_de_filas_y_columnas]
  simpa only [one_mul] using row.mul col

theorem sin_filtro_converge_al_perfil_directo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) (η : ℝ) (ep : 0<η) :
    ∀ᶠ n : ℕ in atTop,∀ z : Cell n,|perfilDirectoSinFiltro j (p ((j:ℝ)/n)) z-aDelLleno p b z|≤η := by
  have pt:=euler_puntual_de_la_rama rama
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama pt
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  let K:=4*M^3*C+4*(M^4/κ^4)*M^4
  filter_upwards [malla_converge_al_lleno rama pt cont j (η/2) (half_pos ep),bal j,
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (1/2) (by norm_num),
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat K)).2 (η/2) (half_pos ep),
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (2*(C:ℝ)))).2 κ rama.kp,
    eventually_ge_atTop 2] with n full grid den small mar nn
  have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have margin : 2*(C:ℝ)≤κ*n := (div_le_iff₀ nr).mp mar.le
  let pn:=p ((j:ℝ)/n)
  have sp:=rama.espacio ((j:ℝ)/n) ⟨by positivity,den.le⟩
  intro z
  have a:=error_del_descarte_y_producto (κ:=lo) (m:=hi) nn sp (show 0<lo from rama.kp)
    (show 1≤hi from rama.m1) grid margin z
  have diff : |perfilDirectoSinFiltro j pn z-blancoNormalizado j pn z|≤K/n := by
    unfold perfilDirectoSinFiltro blancoNormalizado
    rw [←sub_div,abs_div,abs_of_pos nr,abs_sub_comm]
    exact div_le_div_of_nonneg_right a nr.le
  exact (abs_sub_le _ (blancoNormalizado j pn z) _).trans (by linarith only [diff,full z,small])
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_RC_tiende_a_uno
#print axioms ArticuloA.Historias.sin_filtro_converge_al_perfil_directo
