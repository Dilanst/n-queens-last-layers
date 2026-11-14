import ComparacionDesdeElPerfilLleno
open Set MeasureTheory Filter
open scoped NNReal BigOperators Interval Topology
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem cota_inferior_del_coeficiente {P p b x κ M L} (ht : EulerFisica P p x b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (m1 : 1≤M) (xh : (x:ℝ)≤1/2) : 1/(2*M^4)≤b := by
  letI : IsFiniteMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsFiniteMeasure cuadrado := by unfold cuadrado; infer_instance
  have cap : ∀ᵐ z ∂cuadrado,(P.ν z:ℝ)≤b*M^4 := by
    filter_upwards [ht.real,tablero_en_dominio] with z e hz
    rw [e]; exact mul_le_mul_of_nonneg_left (limites_del_producto sp kp.le _ _ hz.1 hz.2).2 ht.coef.le
  have bound:=integral_mono_ae P.masaFinita (integrable_const (b*M^4)) cap
  have area : (∫ _ : ℝ×ℝ,b*M^4 ∂cuadrado)=b*M^4 := by
    rw [integral_de_area_igual_a_iterada (fun _ _ => b*M^4) (integrable_const _)]
    simp [integralTablero,integralFila]
  change P.rho≤_ at bound
  rw [area,ht.masa] at bound
  have mp:=lt_of_lt_of_le zero_lt_one m1
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [bound,xh]

theorem banda_del_valor {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (x : ℝ) (xp : 0<x) (xh : x≤1/2) :
    x*(Real.log (1/(2*M^4))-2*Real.log x)≤(P x).s-(P 0).s ∧
    (P x).s-(P 0).s≤x*(2+Real.log (b 0)-2*Real.log x) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have ok : x∈Icc 0 (1/2:ℝ) := ⟨xp.le,xh⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 zero
  have ht:=rama.euler x ok
  have xx:=Real.toNNReal_pos.mpr xp
  have mp:=lt_of_lt_of_le zero_lt_one rama.m1
  have bb:=cota_inferior_del_coeficiente ht (rama.espacio x ok) rama.kp rama.m1 (by rwa [Real.coe_toNNReal _ xp.le])
  have lg:=Real.log_le_log (by positivity) bb
  have top:=cota_superior_desde_el_lleno full ht (rama.espacio _ zero) (rama.espacio x ok)
    rama.kp rama.lp xx (rama.normaliza 0 zero).1 (rama.normaliza 0 zero).2
  have bot:=soporte_entre_perfiles full ht (rama.espacio _ ok) (rama.espacio _ zero) rama.kp rama.lp xx
  simp only [Real.coe_toNNReal _ xp.le,NNReal.coe_zero,zero_sub,Real.log_div ht.coef.ne' (pow_ne_zero 2 xp.ne'),
    Real.log_pow] at top bot
  refine ⟨?_,top⟩
  calc
    _ ≤ x*(Real.log (b x)-2*Real.log x) := mul_le_mul_of_nonneg_left (sub_le_sub_right lg _) xp.le
    _ ≤ _ := by norm_num1 at bot; linarith only [bot]

theorem continuidad_del_valor_desde_la_rama {P p b κ M L B} (rama : RamaDensa P p b κ M L B) :
    ContinuousWithinAt (fun x => (P x).s) (Icc 0 (1/2:ℝ)) 0 := by
  let I:=Icc 0 (1/2:ℝ)
  have near : ∀ᶠ x in 𝓝[I] 0,x∈I := self_mem_nhdsWithin
  have lm : ContinuousWithinAt (fun x : ℝ => Real.log x*x) I 0 := by
    have r : ContinuousWithinAt (fun x : ℝ => Real.log x*x) (Ioi 0) 0 := by
      simpa only [ContinuousWithinAt,Real.rpow_one,mul_zero] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    exact (continuousWithinAt_Ioi_iff_Ici.mp r).mono (fun _ hx => hx.1)
  have van (A : ℝ) : Tendsto (fun x : ℝ => x*(A-2*Real.log x)) (𝓝[I] 0) (𝓝 0) := by
    have u : ContinuousWithinAt (fun x : ℝ => x*A-2*(Real.log x*x)) I 0 :=
      (continuousWithinAt_id.mul continuousWithinAt_const).sub (continuousWithinAt_const.mul lm)
    convert u.tendsto using 1
    · funext x; ring
    · simp
  have pair : ∀ᶠ x in 𝓝[I] 0,
      x*(Real.log (1/(2*M^4))-2*Real.log x)≤(P x).s-(P 0).s ∧
      (P x).s-(P 0).s≤x*(2+Real.log (b 0)-2*Real.log x) := by
    filter_upwards [near] with x hx
    rcases eq_or_lt_of_le hx.1 with r|r
    · subst x; simp
    · exact banda_del_valor rama x r hx.2
  have conv:=tendsto_of_tendsto_of_tendsto_of_le_of_le' (van (Real.log (1/(2*M^4)))) (van (2+Real.log (b 0)))
    (pair.mono (fun _ h => h.1)) (pair.mono (fun _ h => h.2))
  change Tendsto _ _ _
  simpa only [sub_add_cancel,zero_add] using conv.add (tendsto_const_nhds (x:=(P 0).s))

theorem L1_de_la_rama_y_el_conteo {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (K : ℕ)
    (externo : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0))) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p ((h:ℝ)/n))) (d n) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 zero
  have localcount:=externo (admisibilidad_del_lleno full)
  rw [normalizacion_de_simkin full (rama.espacio 0 zero) rama.kp rama.lp] at localcount
  have count0:=conteo_local_implica_primer_orden localcount
  exact L1_desde_la_familia_canonica rama K (continuidad_del_valor_desde_la_rama rama)
    (sublineal_de_tolerancias count0) (soluciones_eventuales_del_primer_orden count0)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.banda_del_valor
#print axioms ArticuloA.Historias.L1_de_la_rama_y_el_conteo
