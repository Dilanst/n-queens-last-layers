import CuadraturaConModuloDeContinuidad
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open MeasureTheory Filter Set Perfil
open scoped Interval Topology
abbrev cuadradoCerrado := unidadCerrada ×ˢ unidadCerrada

theorem cuadratura_para_pruebas_continuas (t : ℝ×ℝ→ℝ) (ct : ContinuousOn t cuadradoCerrado) :
    Tendsto (fun n => mediaEspacialDeCentros n t) atTop (𝓝 (integralTablero (Function.curry t))) := by
  let F:=fun x => integralFila (Function.curry t) x
  have uc:=(isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous ct
  have fiber (x : ℝ) (hx : x∈unidadCerrada) : ContinuousOn (fun y => t (x,y)) unidadCerrada :=
    ct.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨hx,hy⟩)
  have estimate (x y : ℝ) (hx : x∈unidadCerrada) (hy : y∈unidadCerrada) (d : ℝ)
      (bound : ∀ v∈unidadCerrada,|t (x,v)-t (y,v)|≤d) : |F x-F y|≤d := by
    dsimp only [F,integralFila,Function.curry]
    rw [←intervalIntegral.integral_sub ((fiber x hx).intervalIntegrable_of_Icc zero_le_one)
      ((fiber y hy).intervalIntegrable_of_Icc zero_le_one)]
    have b (v : ℝ) (hv : v∈uIoc (0:ℝ) 1) : ‖t (x,v)-t (y,v)‖≤d := by
      rw [uIoc_of_le zero_le_one] at hv
      exact bound v ⟨hv.1.le,hv.2⟩
    simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const b
  have cF : ContinuousOn F unidadCerrada := by
    apply UniformContinuousOn.continuousOn
    rw [Metric.uniformContinuousOn_iff]
    intro ε ep
    obtain ⟨d,dp,osc⟩:=Metric.uniformContinuousOn_iff.mp uc (ε/2) (half_pos ep)
    refine ⟨d,dp,?_⟩
    intro x hx y hy near
    rw [Real.dist_eq]
    apply lt_of_le_of_lt (estimate _ _ hx hy (ε/2) _) (half_lt_self ep)
    intro v hv
    apply (osc (x,v) ⟨hx,hv⟩ (y,v) ⟨hy,hv⟩ _).le
    simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using near
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let a:=ε/4
  have ap : 0<a := by dsimp [a]; positivity
  obtain ⟨δ,dp,osc⟩:=Metric.uniformContinuousOn_iff.mp uc a ap
  filter_upwards [eventually_gt_atTop 0,(tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat 1)).2 δ dp] with n hn fine
  have nr : 0<(n:ℝ) := by exact_mod_cast hn
  have outer:=error_de_centros_por_oscilacion hn F cF a (by
    intro x hx y hy xy
    apply estimate _ _ hx hy a
    intro v hv
    apply (osc (x,v) ⟨hx,hv⟩ (y,v) ⟨hy,hv⟩ _).le
    rw [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_left (abs_nonneg (x-y))]
    exact xy.trans_lt fine)
  have inner (x : ℝ) (hx : x∈unidadCerrada) :
      |F x-mediaDeCentros n (fun y => t (x,y))|≤a := by
    apply error_de_centros_por_oscilacion hn _ (fiber x hx)
    intro y hy z hz yz
    apply (osc (x,y) ⟨hx,hy⟩ (x,z) ⟨hx,hz⟩ _).le
    rw [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (y-z))]
    exact yz.trans_lt fine
  have summed : |mediaDeCentros n F-mediaEspacialDeCentros n t|≤a := by
    rw [media_espacial_iterada]; unfold mediaDeCentros
    rw [←sub_div,abs_div,abs_of_pos nr,←Finset.sum_sub_distrib]
    apply (div_le_iff₀ nr).mpr
    exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum
      (fun (i : Fin n) _ => inner _ (medio_admisible i.isLt))).trans_eq (by simp [nsmul_eq_mul,mul_comm]))
  rw [Real.dist_eq,abs_sub_comm]
  exact (abs_sub_le _ (mediaDeCentros n F) _).trans_lt (lt_of_le_of_lt (add_le_add outer summed) (by dsimp [a]; linarith))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuadratura_para_pruebas_continuas
