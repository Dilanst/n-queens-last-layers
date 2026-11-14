import MediaEspacialParaPruebasContinuas
import PerfilExteriorConUnaPruebaFirmada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Set Perfil
open scoped Topology
def integralDeLosHuecos (p : FactoresContinuos) (t : ℝ×ℝ→ℝ) :=
  integralTablero (fun r c => t (r,c)*((p.fila r:ℝ)*p.columna c))

theorem masa_del_test_en_la_cuadricula {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L)
    (t : ℝ×ℝ→ℝ) (ct : ContinuousOn t cuadradoCerrado) :
    Tendsto (fun n : ℕ => mediaExterior (fun z : Cell n => valorEnCentro t z*productoRCEnElCentro p z))
      atTop (𝓝 (integralDeLosHuecos p t)) := by
  apply cuadratura_para_pruebas_continuas (fun z => t z*((p.fila z.1:ℝ)*p.columna z.2))
  exact ct.mul (((continua_de_cota lp sp.R.oscilacion).comp continuous_fst.continuousOn (fun _ hz => hz.1)).mul
    ((continua_de_cota lp sp.C.oscilacion).comp continuous_snd.continuousOn (fun _ hz => hz.2)))

theorem limite_del_blanco_por_la_media_exterior {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) (w : (n : ℕ)→Cell n→ℝ)
    {W J : ℝ} (wp : 0≤W) (cap : ∀ n z,|w n z|≤W)
    (avg : Tendsto (fun n : ℕ => mediaExterior (fun z : Cell n => w n z*productoRCEnElCentro (p ((j:ℝ)/n)) z*
      perfilDirectoSinFiltro j (p ((j:ℝ)/n)) z)) atTop (𝓝 J)) :
    Tendsto (fun n : ℕ => blancoInverso j (p ((j:ℝ)/n)) (w n) 1/(n:ℝ)^2) atTop (𝓝 (b 0*J)) := by
  let x:=fun n : ℕ => (j:ℝ)/n
  let main:=fun n : ℕ => (n*escalaDeLasFuentes n j (p (x n)))*
    mediaExterior (fun z => w n z*productoRCEnElCentro (p (x n)) z*perfilDirectoSinFiltro j (p (x n)) z)
  have limit : Tendsto main atTop (𝓝 (b 0*J)) := (escala_de_las_fuentes_al_lleno rama cont j).mul avg
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama (euler_puntual_de_la_rama rama)
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  let D:=4*W*(M^4/κ^4)^2+W*(1+M)*C
  have err : Tendsto (fun n : ℕ => blancoInverso j (p (x n)) (w n) 1/(n:ℝ)^2-main n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [bal j,(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat D)).2 ε ep,
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (j:ℝ))).2 (1/2) (by norm_num),
      (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (2*(C:ℝ)))).2 κ rama.kp,
      eventually_ge_atTop 2] with n balance small den mar nn
    have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have sp:=rama.espacio (x n) ⟨by positivity,den.le⟩
    rw [Real.dist_eq,sub_zero]
    exact (reduccion_a_la_media_exterior (κ:=lo) (m:=hi) nn sp (show 0<lo from rama.kp) balance
      ((div_le_iff₀ nr).mp mar.le) (w n) wp (cap n)).trans_lt small
  simpa only [sub_add_cancel,zero_add] using err.add limit

theorem centro_del_test_continuo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) (t : ℝ×ℝ→ℝ) (ct : ContinuousOn t cuadradoCerrado)
    {T : ℝ} (tp : 0≤T) (bound : ∀ x∈unidadCerrada,∀ y∈unidadCerrada,|t (x,y)|≤T) :
    Tendsto (fun n : ℕ => blancoInverso j (p ((j:ℝ)/n)) (fun z : Cell n => valorEnCentro t z/aDelLleno p b z) 1/(n:ℝ)^2)
      atTop (𝓝 (b 0*integralDeLosHuecos (p 0) t)) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have mp:=mul_pos (rama.euler 0 zero).coef (pow_pos rama.kp 8)
  apply limite_del_blanco_por_la_media_exterior rama cont j _ (W:=T/(b 0*κ^8)) (div_nonneg tp mp.le)
  · intro n z
    have lo:=piso_integral_del_cruce (rama.espacio 0 zero) rama.kp rama.lp (rama.euler 0 zero).coef
      (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
    change b 0*κ^8≤aDelLleno p b z at lo
    rw [abs_div,abs_of_pos (mp.trans_le lo)]
    exact div_le_div₀ tp (bound _ (medio_admisible z.1.isLt) _ (medio_admisible z.2.isLt)) mp lo
  · have err:=exterior_con_prueba_firmada rama cont j t tp bound
    have base:=masa_del_test_en_la_cuadricula (rama.espacio 0 zero) rama.lp t ct
    simpa only [sub_add_cancel,zero_add] using err.add base
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_del_test_en_la_cuadricula
#print axioms ArticuloA.Historias.limite_del_blanco_por_la_media_exterior
#print axioms ArticuloA.Historias.centro_del_test_continuo
