import L1DeLaFamiliaCanonica
import PrimerOrdenPorTolerancias
open Set Filter MeasureTheory
open scoped NNReal Topology BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem entropia_sin_logaritmos_singulares {P p x b κ M L} (h : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) :
    P.s=(1-(x:ℝ))*(-Real.log b-3)-entropiaDeFactores p 1-2*(Real.log x*(x:ℝ)) := by
  rw [entropia_fisica h sp kp lp,h.masa]
  by_cases hx : x=0
  · simp [hx,escalaLog]
  · have nx : (x:ℝ)≠0 := by exact_mod_cast hx
    simp only [escalaLog,if_neg hx,Real.log_div h.coef.ne' (pow_ne_zero 2 nx),Real.log_pow,
      entropiaDeFactores,NNReal.coe_one,Real.log_one]; ring

theorem continuidad_del_valor {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cb : ContinuousWithinAt b (Icc 0 (1/2:ℝ)) 0)
    (fc : ∀ i,∀ t∈rangoF i,ContinuousWithinAt (fun x : ℝ => (factorF (p x) i t:ℝ)) (Icc 0 (1/2:ℝ)) 0) :
    ContinuousWithinAt (fun x => (P x).s) (Icc 0 (1/2:ℝ)) 0 := by
  let I:=Icc 0 (1/2:ℝ)
  have z0 : (0:ℝ)∈I := ⟨le_rfl,by norm_num⟩
  have near : ∀ᶠ x in 𝓝[I] 0,x∈I := self_mem_nhdsWithin
  have ub {x : ℝ} (hx : x∈I) (i : Fin 4) {t} (ht : t∈rangoF i) : (factorF (p x) i t:ℝ)≤M := by
    have s:=rama.espacio x hx
    fin_cases i; exacts [s.Rmax _ ht,s.Cmax _ ht,s.Dmax _ ht,s.Amax _ ht]
  have field (x : ℝ) (i : Fin 4) (t : ℝ) : campoPerfil (p x) 1 i t=Real.log (factorF (p x) i (recorte i t)) := by
    simp [campoPerfil,correccionRC]
  have conv (i : Fin 4) : Tendsto (fun x => ∫ t,campoPerfil (p x) 1 i t ∂marginalRef i) (𝓝[I] 0)
      (𝓝 (∫ t,campoPerfil (p 0) 1 i t ∂marginalRef i)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => |Real.log κ|+|Real.log M|)
    · filter_upwards [near] with x hx
      exact ((campo_perfil_integrable (P x) (rama.espacio _ hx) rama.kp rama.lp 1).medible i).aestronglyMeasurable
    · filter_upwards [near] with x hx
      apply Filter.Eventually.of_forall; intro t
      have low:=((regular_familia (rama.espacio _ hx) i).minimo _ (recorte_dentro i t))
      have lo:=Real.log_le_log rama.kp low
      have hi:=Real.log_le_log (rama.kp.trans_le low) (ub hx i (recorte_dentro i t))
      rw [field,Real.norm_eq_abs,abs_le]
      constructor <;> linarith [le_abs_self (Real.log κ),neg_abs_le (Real.log κ),le_abs_self (Real.log M),
        abs_nonneg (Real.log M),abs_nonneg (Real.log κ)]
    · exact integrable_const _
    · apply Filter.Eventually.of_forall; intro t
      simp_rw [field]
      exact (Real.continuousAt_log (rama.kp.trans_le
        ((regular_familia (rama.espacio 0 z0) i).minimo _ (recorte_dentro i t))).ne').tendsto.comp
          (fc i _ (recorte_dentro i t)).tendsto
  have integ : ContinuousWithinAt (fun x => entropiaDeFactores (p x) 1) I 0 := by
    have total := tendsto_finset_sum Finset.univ (fun i _ => conv i)
    have eq (x : ℝ) (hx : x∈I) := integral_del_campo (rama.espacio _ hx) rama.kp rama.lp 1
    rw [eq 0 z0] at total
    exact total.congr' (near.mono (fun x hx => eq x hx))
  have logb := (Real.continuousAt_log (rama.euler _ z0).coef.ne').comp_continuousWithinAt cb
  have lm : ContinuousWithinAt (fun x : ℝ => Real.log x*x) I 0 := by
    have right : ContinuousWithinAt (fun x : ℝ => Real.log x*x) (Ioi 0) 0 := by
      simpa only [ContinuousWithinAt,Real.rpow_one,mul_zero] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    exact (continuousWithinAt_Ioi_iff_Ici.mp right).mono (fun _ hx => hx.1)
  have cv : ContinuousWithinAt (fun x : ℝ => (1-x)*(-Real.log (b x)-3)-entropiaDeFactores (p x) 1-
      2*(Real.log x*x)) I 0 := ((continuousWithinAt_const.sub continuousWithinAt_id).mul
        (logb.neg.sub continuousWithinAt_const)).sub integ |>.sub (continuousWithinAt_const.mul lm)
  have eq (x : ℝ) (hx : x∈I) : (P x).s=(1-x)*(-Real.log (b x)-3)-entropiaDeFactores (p x) 1-2*(Real.log x*x) := by
    simpa only [Real.coe_toNNReal x hx.1] using entropia_sin_logaritmos_singulares (rama.euler _ hx) (rama.espacio _ hx) rama.kp rama.lp
  exact cv.congr (fun x hx => eq x hx) (eq 0 z0)

theorem L1_del_perfil_y_del_primer_orden {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (K : ℕ)
    (cb : ContinuousWithinAt b (Icc 0 (1/2:ℝ)) 0)
    (fc : ∀ i,∀ t∈rangoF i,ContinuousWithinAt (fun x : ℝ => (factorF (p x) i t:ℝ)) (Icc 0 (1/2:ℝ)) 0)
    (simkin : CotaDePrimerOrden (P 0).s) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p ((h:ℝ)/n))) (d n) :=
  L1_desde_la_familia_canonica rama K (continuidad_del_valor rama cb fc) (sublineal_de_tolerancias simkin)
    (soluciones_eventuales_del_primer_orden simkin)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.continuidad_del_valor
#print axioms ArticuloA.Historias.L1_del_perfil_y_del_primer_orden
