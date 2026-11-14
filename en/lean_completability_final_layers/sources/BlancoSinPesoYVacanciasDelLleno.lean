import MarginalesDeLaReparacionSinPeso
import ElBlancoInversoParaLaUltimaCapa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter Perfil
open scoped Topology
theorem variacion_del_producto {a b c d M e : ℝ} (ac : |a-c|≤e) (bd : |b-d|≤e)
    (bM : |b|≤M) (cM : |c|≤M) (ep : 0≤e) : |a*b-c*d|≤2*M*e := by
  rw [show a*b-c*d=(a-c)*b+c*(b-d) by ring]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul]
  exact (add_le_add (mul_le_mul ac bM (abs_nonneg _) ep)
    (mul_le_mul cM bd (abs_nonneg _) ((abs_nonneg _).trans cM))).trans_eq (by ring)

theorem psi_cambia_con_el_perfil {p q κ M L d} (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L)
    (near : CercaniaDeFactores p q d) (dp : 0≤d) {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    |psiDiagonal p r c-psiDiagonal q r c|≤2*M*d := by
  obtain ⟨rd,ra⟩:=dominios r c hr hc
  apply variacion_del_producto (near 2 _ rd) (near 3 _ ra) _ _ dp
  · rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact sp.Amax _ ra
  · rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact sq.Dmax _ rd

theorem centro_inverso_sin_peso_en_la_malla {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) :
    Tendsto (fun n : ℕ => blancoInverso (n:=n) j (p ((j:ℝ)/n)) (fun _ => 1) 1/(n:ℝ)^2-
      mediaExterior (fun z : Cell n => psiEnElCentro (p 0) z)) atTop (𝓝 0) := by
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama (euler_puntual_de_la_rama rama)
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  let D:=4*(M^4/κ^4)^2+(1+M)*(C:ℝ)
  let U:=(C:ℝ)+j*M
  have mp : 0≤M := zero_le_one.trans rama.m1
  have z0 : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let d:= min 1 (ε/(4*(3*M^2+2*M+1)))
  have dp : 0<d := lt_min zero_lt_one (div_pos ep (by positivity))
  obtain ⟨δ,δp,near⟩:=cont d dp
  filter_upwards [bal j,eventually_ge_atTop 2,
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (min δ (1/2)) (lt_min δp (by norm_num)),
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat U)).2 d dp,
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat D)).2 (ε/2) (half_pos ep),
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (2*(C:ℝ)))).2 κ rama.kp] with n grid nn den sm err mar
  have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  let x:ℝ:=(j:ℝ)/n
  have dom : x∈Icc 0 (1/2:ℝ) := ⟨by dsimp [x]; positivity,den.le.trans (min_le_right ..)⟩
  have sp:=rama.espacio x dom
  let w:=fun (_ : Cell n) => (1:ℝ)
  let g:=fun z : Cell n => psiEnElCentro (p x) z*masaTransversal j (p x) false z.1*masaTransversal j (p x) true z.2
  have raw:=eliminar_filtro_y_reemplazar_vacancias (κ:=lo) (m:=hi) nn sp (show 0<lo from rama.kp) grid
    ((div_le_iff₀ nr).mp mar.le) w zero_le_one (fun _ => by simp [w])
  have e1 : |blancoInverso j (p x) w 1/(n:ℝ)^2-mediaExterior g|≤D/n := by
    unfold mediaExterior
    rw [←suma_sin_peso_por_marginales,←sub_div,abs_div,abs_of_pos (pow_pos nr 2)]
    apply (div_le_div_of_nonneg_right raw (sq_nonneg _)).trans_eq
    dsimp [D,hi,lo]; field_simp; ring
  have small := (near x dom (den.trans_le (min_le_left ..))).2
  have one (col : Bool) (z : Fin n) : |masaTransversal j (p x) col z-1|≤d :=
    (balance_de_una_transversal (by omega) sp grid col z).trans sm.le
  have e2 : |mediaExterior g-mediaExterior (fun z : Cell n => psiEnElCentro (p 0) z)|≤(3*M^2+2*M)*d := by
    apply continuidad_de_la_media_exterior _ _ _ (by positivity)
    intro z
    have hr:=medio_admisible z.1.isLt
    have hc:=medio_admisible z.2.isLt
    let R:=masaTransversal j (p x) false z.1
    let S:=masaTransversal j (p x) true z.2
    have sr : |S|≤2 := by
      have q:=abs_le.mp (one true z.2); have dl : d≤1 := min_le_left ..; exact abs_le.mpr (by dsimp [S]; constructor <;> linarith [q.1,q.2])
    have rs : |R*S-1|≤3*d := by
      rw [show R*S-1=(R-1)*S+(S-1) by ring]
      apply (abs_add_le ..).trans
      rw [abs_mul]
      linarith only [mul_le_mul (one false z.1) sr (abs_nonneg _) dp.le,one true z.2]
    obtain ⟨rd,ra⟩:=dominios _ _ hr hc
    have cap : |psiEnElCentro (p x) z|≤M^2 := by
      unfold psiEnElCentro psiDiagonal; rw [abs_of_nonneg (by positivity),pow_two]
      exact mul_le_mul (sp.Dmax _ rd) (sp.Amax _ ra) (NNReal.coe_nonneg _) mp
    have dc:=psi_cambia_con_el_perfil sp (rama.espacio 0 z0) small dp.le hr hc
    change |psiEnElCentro (p x) z*R*S-psiEnElCentro (p 0) z|≤_
    rw [show psiEnElCentro (p x) z*R*S-psiEnElCentro (p 0) z=
      psiEnElCentro (p x) z*(R*S-1)+(psiEnElCentro (p x) z-psiEnElCentro (p 0) z) by ring]
    apply (abs_add_le ..).trans; rw [abs_mul]
    exact (add_le_add (mul_le_mul cap rs (abs_nonneg _) (sq_nonneg _)) dc).trans_eq (by ring)
  have dd : (3*M^2+2*M)*d≤ε/4 := by
    calc _ ≤ (3*M^2+2*M+1)*d := mul_le_mul_of_nonneg_right (by linarith) dp.le
         _ ≤ (3*M^2+2*M+1)*(ε/(4*(3*M^2+2*M+1))) := mul_le_mul_of_nonneg_left (min_le_right ..) (by positivity)
         _ = _ := by field_simp; ring
  rw [Real.dist_eq,sub_zero]
  exact (abs_sub_le _ (mediaExterior g) _).trans_lt (by linarith only [e1,err,e2,dd,ep])
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.variacion_del_producto
#print axioms ArticuloA.Historias.psi_cambia_con_el_perfil
#print axioms ArticuloA.Historias.centro_inverso_sin_peso_en_la_malla
