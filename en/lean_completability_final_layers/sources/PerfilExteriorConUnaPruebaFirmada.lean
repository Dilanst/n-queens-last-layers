import BlancoSinPesoYVacanciasDelLleno
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Set Perfil
open scoped Topology
def valorEnCentro {n} (t : ℝ×ℝ→ℝ) (z : Cell n) := t (medio n z.1.val,medio n z.2.val)

theorem exterior_con_prueba_firmada {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) (t : ℝ×ℝ→ℝ) {T : ℝ} (tp : 0≤T)
    (cap : ∀ x∈unidadCerrada,∀ y∈unidadCerrada,|t (x,y)|≤T) :
    Tendsto (fun n : ℕ => mediaExterior (fun z : Cell n => (valorEnCentro t z/aDelLleno p b z)*
      productoRCEnElCentro (p ((j:ℝ)/n)) z*perfilDirectoSinFiltro j (p ((j:ℝ)/n)) z)-
      mediaExterior (fun z : Cell n => valorEnCentro t z*productoRCEnElCentro (p 0) z)) atTop (𝓝 0) := by
  let m:=b 0*κ^8
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bp:=(rama.euler 0 zero).coef
  have mp : 0<m := mul_pos bp (pow_pos rama.kp _)
  have M0 : 0≤M := zero_le_one.trans rama.m1
  let K:=T*(M^2/m+2*M)
  have kp : 0≤K := by dsimp [K]; positivity
  apply Metric.tendsto_nhds.mpr; intro ε ep
  let d:=ε/(2*(K+1))
  have dp : 0<d := div_pos ep (by positivity)
  obtain ⟨δ,δp,near⟩:=cont d dp
  filter_upwards [sin_filtro_converge_al_perfil_directo rama cont j d dp,
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (min δ (1/2)) (lt_min δp (by norm_num))]
    with n good den
  let x:ℝ:=(j:ℝ)/n
  have dom : x∈Icc 0 (1/2:ℝ) := ⟨by dsimp [x]; positivity,den.le.trans (min_le_right ..)⟩
  have sp:=rama.espacio x dom
  have sq:=rama.espacio 0 zero
  have clos:=(near x dom (den.trans_le (min_le_left ..))).2
  rw [Real.dist_eq,sub_zero]
  apply lt_of_le_of_lt (continuidad_de_la_media_exterior _ _ (K*d) (mul_nonneg kp dp.le) _) _
  · intro z
    let R:=productoRCEnElCentro (p x) z
    let R₀:=productoRCEnElCentro (p 0) z
    let A:=aDelLleno p b z
    let S:=perfilDirectoSinFiltro j (p x) z
    have hr:=medio_admisible z.1.isLt
    have hc:=medio_admisible z.2.isLt
    have lo : m≤A := piso_integral_del_cruce sq rama.kp rama.lp bp hr hc
    have pos:=mp.trans_le lo
    have upper : |R|≤M^2 := by
      change |(_ : ℝ)*_|≤M^2
      rw [abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)),pow_two]
      exact mul_le_mul (sp.Rmax _ hr) (sp.Cmax _ hc) (NNReal.coe_nonneg _) M0
    have cross : |R-R₀|≤2*M*d := by
      apply variacion_del_producto (clos 0 _ hr) (clos 1 _ hc) _ _ dp.le
      · rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact sp.Cmax _ hc
      · rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact sq.Rmax _ hr
    let v:=valorEnCentro t z
    have boundV : |v|≤T := cap _ hr _ hc
    change |v/A*R*S-v*R₀|≤K*d
    rw [show v/A*R*S-v*R₀=v*((S-A)*(R/A)+(R-R₀)) by field_simp [pos.ne']; ring,abs_mul]
    apply (mul_le_mul boundV (abs_add_le ..) (abs_nonneg _) tp).trans
    rw [abs_mul,abs_div,abs_of_pos pos]
    have step:=mul_le_mul (good z) (div_le_div₀ (sq_nonneg M) upper mp lo) (by positivity : 0≤|R|/A) dp.le
    apply (mul_le_mul_of_nonneg_left (add_le_add step cross) tp).trans_eq
    unfold K; ring
  · calc K*d ≤ (K+1)*d := mul_le_mul_of_nonneg_right (by linarith) dp.le
         _ = ε/2 := by dsimp [d]; field_simp; ring
         _ < ε := half_lt_self ep
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.exterior_con_prueba_firmada
