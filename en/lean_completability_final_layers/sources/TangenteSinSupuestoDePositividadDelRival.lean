import ValorDeEulerIntegrado
open MeasureTheory Filter Set
open scoped NNReal BigOperators
namespace ArticuloA.Perfil
noncomputable section

theorem xlogx_tangente {x y : ℝ} (hx : 0<x) (hy : 0≤y) :
    y+y*Real.log x-x≤xlogx y := by
  rcases eq_or_lt_of_le hy with z|p
  · subst y; simp [xlogx,hx.le]
  · have h:=Real.log_le_sub_one_of_pos (div_pos hx p)
    rw [Real.log_div hx.ne' p.ne'] at h
    have e:=mul_le_mul_of_nonneg_right h p.le
    rw [sub_mul,sub_mul,div_mul_cancel₀ _ p.ne',one_mul] at e
    unfold xlogx; linarith only [e]

instance finita_marginal (i : Fin 4) : IsFiniteMeasure (marginalRef i) := by
  fin_cases i <;> unfold marginalRef <;> infer_instance

theorem TableroMedido.m_integrable (P : TableroMedido) (i : Fin 4) :
    Integrable (fun x => (P.m i x:ℝ)) (marginalRef i) := by
  apply (integrable_const (μ:=marginalRef i) (1:ℝ)).mono' (P.ley.densidadLinea i).coe_nnreal_real.aestronglyMeasurable
  filter_upwards [P.admisible i] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (NNReal.coe_nonneg _)] using hx

theorem TableroMedido.u_integrable (P : TableroMedido) (i : Fin 4) :
    Integrable (P.u i) (marginalRef i) := (integrable_const 1).sub (P.m_integrable i)

theorem desplazamiento_de_vacancia (P Q : TableroMedido) (i : Fin 4) :
    (∫ x,Q.u i x ∂marginalRef i)-(∫ x,P.u i x ∂marginalRef i)=P.rho-Q.rho := by
  simp only [TableroMedido.u,integral_sub (integrable_const _) (P.m_integrable i),
    integral_sub (integrable_const _) (Q.m_integrable i),masa_de_cada_linea Q.ley,masa_de_cada_linea P.ley,
    TableroMedido.rho]; ring

theorem tangente_integrada {X : Type*} [MeasurableSpace X] (μ : Measure X) (p q v : X→ℝ)
    (ip : Integrable p μ) (iq : Integrable q μ) (iv : Integrable (fun z => q z*v z) μ)
    (ie : Integrable (fun z => xlogx (q z)) μ) (pos : ∀ᵐ z ∂μ,0<p z)
    (nn : ∀ᵐ z ∂μ,0≤q z) (campo : ∀ᵐ z ∂μ,Real.log (p z)=v z) :
    (∫ z,q z ∂μ)+(∫ z,q z*v z ∂μ)-(∫ z,p z ∂μ)≤∫ z,xlogx (q z) ∂μ := by
  have plus : Integrable (fun z => q z+q z*v z) μ := iq.add iv
  rw [←integral_add iq iv,←integral_sub plus ip]
  apply integral_mono_ae ((iq.add iv).sub ip) ie
  filter_upwards [pos,nn,campo] with z hp hq eq
  change q z+q z*v z-p z≤xlogx (q z)
  rw [←eq]; exact xlogx_tangente hp hq

theorem soporte_variacional (P Q : TableroMedido) {v} (hP : CampoIntegrable P v) (hQ : CampoIntegrable Q v)
    (l : ℝ) (p : ∀ᵐ z ∂cuadrado,0<(P.ν z:ℝ)) (u : ∀ i,∀ᵐ x ∂marginalRef i,0<P.u i x)
    (euler : ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=l+∑ i : Fin 4,v i (coord i z))
    (vu : ∀ i,∀ᵐ x ∂marginalRef i,Real.log (P.u i x)=v i x)
    (iν : Integrable (fun z => xlogx (Q.ν z)) cuadrado)
    (iu : ∀ i,Integrable (fun x => xlogx (Q.u i x)) (marginalRef i)) :
    Q.s-P.s≤ -(Q.rho-P.rho)*l := by
  have int : Integrable (fun z => (Q.ν z:ℝ)*(l+∑ i : Fin 4,v i (coord i z))) cuadrado := by
    simp_rw [mul_add,Finset.mul_sum]
    exact (Q.masaFinita.mul_const l).add (integrable_finset_sum _ (fun i _ => hQ.ocupada i))
  have dens:=tangente_integrada cuadrado (fun z => (P.ν z:ℝ)) (fun z => (Q.ν z:ℝ)) _ P.masaFinita Q.masaFinita int
    iν p (Eventually.of_forall (fun z => NNReal.coe_nonneg _)) euler
  rw [integrar_campo_del_tablero Q hQ l] at dens
  change Q.rho+(Q.rho*l+_)-P.rho≤_ at dens
  have loc (i : Fin 4) : P.rho-Q.rho+(∫ x,Q.u i x*v i x ∂marginalRef i)≤∫ x,xlogx (Q.u i x) ∂marginalRef i := by
    have t:=tangente_integrada _ _ _ _ (P.u_integrable i) (Q.u_integrable i) (hQ.libre i) (iu i) (u i)
      ((Q.admisible i).mono (fun x hx => sub_nonneg.mpr hx)) (vu i)
    linarith only [t,desplazamiento_de_vacancia P Q i]
  have total:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => loc i)
  rw [Finset.sum_add_distrib] at total
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at total
  have val:=valor_de_euler P hP l euler (fun i => (vu i).mono (fun x hx => by simp [xlogx,hx]))
  rw [val,←complementar_campo Q hQ]
  change (-3*Q.rho-_-_)-_≤_
  linarith only [dens,total]
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.soporte_variacional
