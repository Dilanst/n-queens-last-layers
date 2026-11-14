import MediasGeometricasDeLosFactores
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem balance_de_los_logaritmos_sin_escala {P p x b} (e : EulerFisica P p x b)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    Integrable (fun z=>xlogx (P.ν z)) cuadrado ∧
    (∫ z,xlogx (P.ν z) ∂cuadrado)=P.rho*log b+
      ∑ i : Fin 4,∫ s,(P.m i s:ℝ)*log (campoR15 p i s) ∂marginalRef i := by
  let w i s:=log (campoR15 p i s)
  have pp i s : 0<campoR15 p i s := pos i _ (recorte_dentro i s)
  have cc:=campo_continuo_por_recorte cp
  have wc i : Continuous (w i) := (cc i).log (fun s=>(pp i s).ne')
  have coordc (i : Fin 4) : Continuous (coord i) := by
    fin_cases i; exacts [continuous_fst,continuous_snd,continuous_fst.sub continuous_snd,continuous_fst.add continuous_snd]
  let U:=pesoDePruebaB33 p b
  have uc : Continuous U := (((continuous_const.mul ((cc 0).comp continuous_fst)).mul ((cc 1).comp continuous_snd)).mul
    ((cc 2).comp (continuous_fst.sub continuous_snd))).mul ((cc 3).comp (continuous_fst.add continuous_snd))
  have uv : (fun z=>(P.ν z:ℝ))=ᵐ[cuadrado] U := densidad_en_factores_recortados e
  have wi i : Integrable (fun z=>(P.ν z:ℝ)*w i (coord i z)) cuadrado :=
    (integral_cuadrada_de_una_continua (uc.mul ((wc i).comp (coordc i)))).congr
      (uv.mono (fun z h=>congrArg (·*w i (coord i z)) h.symm))
  have logeq : ∀ᵐ z ∂cuadrado,xlogx (P.ν z)=(P.ν z:ℝ)*log b+
      ∑ i : Fin 4,(P.ν z:ℝ)*w i (coord i z) := by
    filter_upwards [densidad_en_factores_recortados e] with z hz
    have hl:=log_del_producto (y:=fun i=>campoR15 p i (coord i z)) e.coef (fun i=>pp i _) hz
    simp only [xlogx,hl,mul_add,Finset.mul_sum,w]
  have si:=integrable_finset_sum Finset.univ (fun i _=>wi i)
  refine ⟨((P.masaFinita.mul_const (log b)).add si).congr (logeq.mono (fun _ h=>h.symm)),?_⟩
  rw [integral_congr_ae logeq,integral_add (P.masaFinita.mul_const _) si,integral_mul_const,integral_finset_sum _ (fun i _=>wi i)]
  change P.rho*log b+_ = P.rho*log b+_
  congr 1
  exact Finset.sum_congr rfl (fun i _=>adjuncion P.ley i (w i) (wc i).measurable)

theorem signo_del_trabajo_transversal {P p x b} (e : EulerFisica P p x b)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (rc : i.val<2) :
    (∫ s,(P.m i s:ℝ)*log (campoR15 p i s) ∂marginalRef i)≤(1-(x:ℝ))*∫ s,log (campoR15 p i s) ∂unidad := by
  have ref : marginalRef i=unidad := by
    rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
  let r:=campoR15 p i
  have rp s : 0<r s := pos i _ (recorte_dentro i s)
  have cc:=campo_continuo_por_recorte cp i
  have lc : Continuous (fun s=>log (r s)) := cc.log (fun s=>(rp s).ne')
  have li:=integral_de_etiqueta_de_una_continua i lc
  have mi : Integrable (fun s=>(1-coefLinea x i*r s)*log (r s)) (marginalRef i) :=
    integral_de_etiqueta_de_una_continua i ((continuous_const.sub (continuous_const.mul cc)).mul lc)
  rw [←ref,←integral_const_mul]
  apply (integral_congr_ae ((masa_de_linea_normalizada e i).mono (fun s h=>congrArg (·*log (r s)) h))).le.trans
  apply integral_mono_ae mi (li.const_mul _)
  filter_upwards with s
  change (1-coefLinea x i*r s)*log (r s)≤(1-(x:ℝ))*log (r s)
  simp only [coefLinea,if_pos rc]
  have h : 0≤(r s-1)*log (r s) := by
    by_cases hs : 1≤r s
    · exact mul_nonneg (sub_nonneg.mpr hs) (log_nonneg hs)
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_ge hs)) (log_nonpos (rp s).le (le_of_not_ge hs))
  nlinarith only [mul_nonneg x.coe_nonneg h]

theorem masa_acotada_por_las_dos_medias {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (d : 0<1-(x:ℝ))
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    1-(x:ℝ)≤b*mediaGeometrica (campoR15 p 0)*mediaGeometrica (campoR15 p 1) := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance
  obtain ⟨intg,bal⟩:=balance_de_los_logaritmos_sin_escala e cp pos
  have mass : (∫ z,(P.ν z:ℝ) ∂cuadrado)=1-(x:ℝ) := e.masa
  have j:=jensen_entropia_de_una_densidad (Eventually.of_forall (fun z=>(P.ν z).coe_nonneg))
    P.masaFinita intg (mass ▸ d)
  have ob (i : Fin 4) (hi : ¬i.val<2) : (∫ s,(P.m i s:ℝ)*log (campoR15 p i s) ∂marginalRef i)≤0 := by
    apply integral_nonpos_of_ae
    filter_upwards [(vacancia_fisica_y_logaritmo e xp cp pos i).2.2.2.2] with s hs
    simp only [holguraInteriorR5,coefLinea,if_neg hi,one_mul] at hs
    exact mul_nonpos_of_nonneg_of_nonpos (P.m i s).coe_nonneg (log_nonpos (pos i _ (recorte_dentro i s)).le hs)
  rw [mass,bal,Fin.sum_univ_four,e.masa] at j
  have t0:=signo_del_trabajo_transversal e cp pos 0 (by decide)
  have t1:=signo_del_trabajo_transversal e cp pos 1 (by decide)
  have t2:=ob 2 (by decide); have t3:=ob 3 (by decide)
  unfold xlogx at j
  have h : log (1-(x:ℝ))≤log b+(∫ s,log (campoR15 p 0 s) ∂unidad)+(∫ s,log (campoR15 p 1 s) ∂unidad) := by
    apply le_of_mul_le_mul_left (a:=1-(x:ℝ)) _ d
    linarith only [j,t0,t1,t2,t3]
  simpa only [exp_log d,exp_add,exp_log e.coef,mediaGeometrica] using exp_le_exp.mpr h

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.balance_de_los_logaritmos_sin_escala
#print axioms ArticuloA.Historias.signo_del_trabajo_transversal
#print axioms ArticuloA.Historias.masa_acotada_por_las_dos_medias
