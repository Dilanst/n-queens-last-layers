import IdentidadesDeLaDensidadSeparada
import VacanciasDiagonalesEnLaMedidaOcupada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
theorem transversal_integrable {p κ M L} (s : ControlEspacial p κ M L) (lp : 0≤L) (i : Fin 4) :
    Integrable (campoR15 p i) unidad := by
  apply integrable_acotada_probabilidad (continuo_de_campo s lp i).measurable (C:=M)
  intro t
  exact (abs_of_nonneg (a:=campoR15 p i t) (NNReal.coe_nonneg _)).le.trans (banda_de_campo s i t).2

theorem distancia_de_la_marginal_de_V {p q b c κ M L}
    (gp : NormalizacionR15 p) (gq : NormalizacionR15 q)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (lp : 0≤L)
    (i : Fin 4) (rc : i.val<2) :
    distanciaEnMedida unidad (fun s=>b*campoR15 p i s) (fun s=>c*campoR15 q i s)≤
      distanciaEnMedida cuadrado (densidadSeparada p b) (densidadSeparada q c) := by
  let f:=campoR15 p i
  let g:=campoR15 q i
  let w:=fun s=>if c*g s≤b*f s then (1:ℝ) else -1
  have fw:Measurable w:=Measurable.ite (measurableSet_le (measurable_const.mul (continuo_de_campo sq lp i).measurable)
    (measurable_const.mul (continuo_de_campo sp lp i).measurable)) measurable_const measurable_const
  have norm s : ‖w s‖≤1 := by dsimp [w]; split_ifs <;> norm_num
  have t1 {a : ℝ→ℝ} (ha : Integrable a unidad) : Integrable (fun s=>a s*w s) unidad := by
    simpa only [mul_comm] using ha.bdd_mul fw.aestronglyMeasurable ⟨1,norm⟩
  have t2 {a : ℝ×ℝ→ℝ} (ha : Integrable a cuadrado) : Integrable (fun z=>a z*w (coord i z)) cuadrado := by
    simpa only [mul_comm] using ha.bdd_mul (fw.comp (coord_medible i)).aestronglyMeasurable ⟨1,fun z=>norm (coord i z)⟩
  have eq1 (s : ℝ) : |b*f s-c*g s|=b*(f s*w s)-c*(g s*w s) := by
    dsimp only [w]; split_ifs with hx
    · rw [abs_of_nonneg (sub_nonneg.mpr hx)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hx))]; ring
  change (∫ s,|b*f s-c*g s| ∂unidad)≤_
  simp_rw [eq1]
  rw [integral_sub ((t1 (transversal_integrable sp lp i)).const_mul b)
    ((t1 (transversal_integrable sq lp i)).const_mul c), integral_const_mul,integral_const_mul]
  change b*(∫ t,campoR15 p i t*w t ∂unidad)-c*(∫ t,campoR15 q i t*w t ∂unidad)≤_
  rw [←proyeccion_de_V_con_prueba p b gp i rc w,←proyeccion_de_V_con_prueba q c gq i rc w,
    ←integral_sub (t2 (separada_integrable b sp lp)) (t2 (separada_integrable c sq lp))]
  apply integral_mono ((t2 (separada_integrable b sp lp)).sub (t2 (separada_integrable c sq lp)))
    ((separada_integrable b sp lp).sub (separada_integrable c sq lp)).abs
  intro z
  simp only [Pi.sub_apply]
  rw [←sub_mul]
  apply (le_abs_self _).trans
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (norm (coord i z)) (abs_nonneg (densidadSeparada p b z-densidadSeparada q c z))

theorem estabilidad_de_transversal_R15 {p q b c κ M L}
    (gp : NormalizacionR15 p) (gq : NormalizacionR15 q)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (lp : 0≤L)
    (bp : 0<b) (i : Fin 4) (rc : i.val<2) :
    b*(∫ t,errorEntreCamposR15 p q i t ∂unidad)≤2*distanciaEnMedida cuadrado (densidadSeparada p b) (densidadSeparada q c) := by
  let f:=campoR15 p i
  let g:=campoR15 q i
  have per (t : ℝ) : b*errorEntreCamposR15 p q i t≤|b*f t-c*g t|+|b-c| *g t := by
    change b*|f t-g t|≤_
    have eq : b*(f t-g t)=(b*f t-c*g t)+(c-b)*g t := by ring
    calc
      _ = |b*(f t-g t)| := by rw [abs_mul,abs_of_pos bp]
      _ ≤ |b*f t-c*g t|+|(c-b)*g t| := eq ▸ abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_sub_comm c b,abs_of_nonneg (a:=g t) (NNReal.coe_nonneg _)]
  have im:=((transversal_integrable sp lp i).const_mul b |>.sub ((transversal_integrable sq lp i).const_mul c)).abs
  have iw:=integrable_acotada_probabilidad (μ:=unidad) (continua_diferencia_de_linea sp sq lp i).measurable
    (error_de_linea_acotado sp sq i)
  have val:=integral_mono (iw.const_mul b) (im.add ((transversal_integrable sq lp i).const_mul |b-c|)) per
  simp only [Pi.add_apply] at val
  rw [integral_const_mul,integral_add im ((transversal_integrable sq lp i).const_mul _),
    integral_const_mul,gq i rc,mul_one] at val
  have iv:=distancia_de_la_marginal_de_V gp gq sp sq lp i rc (b:=b) (c:=c)
  have ib:=estabilidad_del_normalizador gp gq sp sq lp (b:=b) (c:=c)
  exact val.trans ((add_le_add iv ib).trans_eq (by ring))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.transversal_integrable
#print axioms ArticuloA.Historias.distancia_de_la_marginal_de_V
#print axioms ArticuloA.Historias.estabilidad_de_transversal_R15
