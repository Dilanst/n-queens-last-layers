import ValorDeAbsorcionEnCoordenadasCartesianas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- A single supporting line suffices for the lower direction. -/
theorem valor_interior_al_menos_valor_lleno {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (kp : 0<κ) (mm : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    {x : ℝ} (xp : 0<x) (xh : x≤1/2) (tiny : x^2 ≤ 1/(2*M^4)) :
    (P 0).s≤(P x).s := by
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ):=⟨le_rfl,by norm_num⟩
  have xx : x∈Icc 0 (1/2:ℝ):=⟨xp.le,xh⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0):=by simpa using eq 0 z
  have eo:=eq x xx
  have xe:=Real.coe_toNNReal x xp.le
  have bd:=cota_inferior_del_coeficiente eo (sp x xx) kp mm (by rwa [xe])
  have lg:=Real.log_nonneg ((one_le_div (by positivity : 0<x^2)).mpr (tiny.trans bd))
  obtain ⟨qi,ui⟩:=entropias_del_optimo_integrables full (sp 0 z) kp lp
  have sup:=soporte_del_perfil_positivo eo (sp x xx) kp lp (Real.toNNReal_pos.mpr xp) (P 0) qi ui
  rw [full.masa,eo.masa,xe,NNReal.coe_zero] at sup
  nlinarith only [sup,mul_nonneg xp.le lg]

/-- The test densities and the compared value are chosen before any law of G. -/
theorem existe_perfil_para_la_cota_inferior :
    ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ M L : ℝ),
      0<κ ∧ κ≤1 ∧ 1≤M ∧ 0≤L ∧ NormalizacionR15 (p 0) ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)) ∧
      (∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) ∧
      ∀ x : ℝ,0<x → x≤1/2 → x^2≤1/(2*M^4) → sSup valoresCartesianosDeAbsorcion≤(P x).s := by
  obtain ⟨P,p,b,κ,M,L,kp,k1,mm,lp,g,eq,sp⟩:=existe_rama_normalizada_del_articulo
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ):=⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0):=by simpa using eq 0 z
  refine ⟨P,p,b,κ,M,L,kp,k1,mm,lp,g,eq,sp,?_⟩
  rw [los_dos_dominios_de_valores_finitos_coinciden,(extremo_alcanza_el_supremo kp mm lp eq sp g).csSup_eq,
    normalizacion_de_simkin full (sp 0 z) kp lp]
  exact fun _ xp xh tiny=>valor_interior_al_menos_valor_lleno kp mm lp eq sp xp xh tiny

/-- The endpoint and the interior use the supremum of the same functional. -/
theorem el_supremo_cartesiano_interior_domina_al_lleno :
    ∃ η : ℝ,0<η ∧ ∀ x : ℝ,0<x → x≤η →
      sSup valoresCartesianosDeAbsorcion≤sSup (valoresCartesianosEnMasa (1-x)) := by
  obtain ⟨P,p,b,κ,M,L,kp,_,mm,lp,_,eq,sp,lower⟩:=existe_perfil_para_la_cota_inferior
  let β:=1/(2*M^4)
  have mp : 0<M:=zero_lt_one.trans_le mm
  have bp : 0<β:=by dsimp [β]; positivity
  refine ⟨min (1/2) β,lt_min (by norm_num) bp,?_⟩
  intro x xp small
  have half:=small.trans (min_le_left _ _)
  have xx : x∈Icc 0 (1/2:ℝ):=⟨xp.le,half⟩
  have tiny : x^2≤β:=(show x^2≤x by nlinarith [mul_nonneg xp.le (show 0≤1-x by linarith)]).trans
    (small.trans (min_le_right _ _))
  have e:=eq x xx
  have mass : (P x).rho=1-x:=by simpa [Real.coe_toNNReal _ xp.le] using e.masa
  obtain ⟨qi,ui⟩:=entropias_del_optimo_integrables e (sp x xx) kp lp
  have top : IsGreatest (valoresMedidosEnMasa (1-x)) (P x).s:=by
    refine ⟨⟨P x,mass,qi,ui,rfl⟩,?_⟩
    rintro _ ⟨Q,hq,qj,uj,rfl⟩
    have h:=soporte_del_perfil_positivo e (sp x xx) kp lp (Real.toNNReal_pos.mpr xp) Q qj uj
    rw [mass,hq,sub_self,neg_zero,zero_mul] at h
    linarith
  rw [conjuntos_de_valores_en_cada_masa,top.csSup_eq]
  exact lower x xp half tiny
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.el_supremo_cartesiano_interior_domina_al_lleno
#print axioms ArticuloA.Historias.valor_interior_al_menos_valor_lleno
#print axioms ArticuloA.Historias.existe_perfil_para_la_cota_inferior
