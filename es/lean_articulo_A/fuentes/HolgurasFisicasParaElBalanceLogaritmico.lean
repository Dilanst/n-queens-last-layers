import IdentidadR5ParaElTableroInterior
import ControlIntegralDeLosLogaritmosOblicuos
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Real
open scoped Topology Interval
def holguraInteriorR5 (p : FactoresContinuos) (x : ℝ≥0) (i : Fin 4) (s : ℝ) := coefLinea x i*campoR15 p i s

theorem vacancia_fisica_y_logaritmo {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) :
    Continuous (holguraInteriorR5 p x i) ∧ (∀ s,0<holguraInteriorR5 p x i s) ∧
    (∀ s,campoPerfil p x i s=log (holguraInteriorR5 p x i s)) ∧
    (∀ᵐ s ∂marginalRef i,(P.m i s:ℝ)=1-holguraInteriorR5 p x i s) ∧
    ∀ᵐ s ∂marginalRef i,holguraInteriorR5 p x i s≤1 := by
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have coef : 0<coefLinea x i := by unfold coefLinea; split_ifs <;> first | exact xr | exact zero_lt_one
  have pp (s : ℝ) : 0<campoR15 p i s := pos i _ (recorte_dentro i s)
  have occ:=masa_de_linea_normalizada e i
  refine ⟨continuous_const.mul (campo_continuo_por_recorte cp i),fun s=>mul_pos coef (pp s),?_,occ,?_⟩
  · intro s
    rw [holguraInteriorR5,log_mul coef.ne' (pp s).ne']
    change correccionRC x i+_ = log (coefLinea x i)+_
    by_cases rc : i.val<2 <;> simp [correccionRC,coefLinea,rc,campoR15]
  · filter_upwards [occ] with s hs
    change coefLinea x i*campoR15 p i s≤1
    linarith only [hs,(P.m i s).coe_nonneg]

theorem covarianza_en_cada_transversal {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (rc : i.val<2) : 0≤ -terminoDeR5 P p x i := by
  let u:=holguraInteriorR5 p x i
  have md : marginalDelTestigo i=fun _=>1 := by fin_cases i <;> first | rfl | exact False.elim (by norm_num at rc)
  obtain ⟨uc,up,w,occ,_⟩:=vacancia_fisica_y_logaritmo e xp cp pos i
  have ref : marginalRef i=unidad := by
    fin_cases i <;> first | exact Measure.restrict_congr_set Ioc_ae_eq_Icc | exact False.elim (by norm_num at rc)
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsProbabilityMeasure (marginalRef i):=by rw [ref]; infer_instance
  have ui:=integral_de_etiqueta_de_una_continua i uc
  have mass : (∫ s,u s ∂marginalRef i)=(x:ℝ) := by
    have h:=masa_de_cada_linea P.ley i
    change (∫ s,(P.m i s:ℝ) ∂marginalRef i)=P.rho at h
    rw [integral_congr_ae occ,integral_sub (integrable_const _) ui,e.masa] at h
    simp only [integral_const,measureReal_univ_eq_one,one_smul] at h
    linarith only [h]
  have wi : Integrable (fun s=>(u s-(x:ℝ))*log (u s)) (marginalRef i) :=
    integral_de_etiqueta_de_una_continua i ((uc.sub continuous_const).mul (uc.log (fun s=>(up s).ne')))
  have cv:=covarianza_de_una_holgura_y_su_log (marginalRef i) (show 0<(x:ℝ) by exact_mod_cast xp)
    (Eventually.of_forall up) ui mass wi
  have key : terminoDeR5 P p x i = -(∫ s,(u s-(x:ℝ))*log (u s) ∂marginalRef i) := by
    rw [←integral_neg]; apply integral_congr_ae
    filter_upwards [occ] with s hs
    change ((P.m i s:ℝ)-(1-(x:ℝ))*marginalDelTestigo i s)*campoPerfil p x i s = -((u s-(x:ℝ))*log (u s))
    rw [hs,md,w]; dsimp only [u]; ring
  linarith only [key,cv]

theorem rango_del_testigo_sobre_una_oblicua (a : Bool) {s : ℝ} (sr : |s|≤1) :
    0≤proyeccionDelTestigo a s ∧ proyeccionDelTestigo a s≤9/10 := by
  refine ⟨intervalIntegral.integral_nonneg (sub_nonneg.mpr sr) (fun t _=>?_),ambas_proyecciones_del_testigo a sr⟩
  exact (by norm_num : (0:ℝ)≤4/5).trans (cotas_del_testigo_DEF _ _).1
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.vacancia_fisica_y_logaritmo
#print axioms ArticuloA.Historias.covarianza_en_cada_transversal
#print axioms ArticuloA.Historias.rango_del_testigo_sobre_una_oblicua
