import EntradaDeConteoParaElPerfilCentrado
open Set MeasureTheory Filter
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

/-- The four comparison vacancies need not come from a single feasible board. -/
theorem cota_dual_con_referencias (P Q : TableroMedido) (u v : Fin 4→ℝ→ℝ) (l : ℝ)
    (hq : CampoIntegrable Q v) (pos : ∀ᵐ z ∂cuadrado,0<(P.ν z:ℝ))
    (euler : ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=l+∑ i : Fin 4,v i (coord i z))
    (ui : ∀ i,Integrable (u i) (marginalRef i)) (up : ∀ i,∀ᵐ t ∂marginalRef i,0<u i t)
    (eq : ∀ i,∀ᵐ t ∂marginalRef i,Real.log (u i t)=v i t)
    (ent : Integrable (fun z => xlogx (Q.ν z)) cuadrado ∧
      ∀ i,Integrable (fun t => xlogx (Q.u i t)) (marginalRef i)) :
    Q.s ≤ -3*Q.rho-(Q.rho-P.rho)-Q.rho*l-(∑ i,∫ t,v i t ∂marginalRef i)-
      (∑ i,((∫ t,Q.u i t ∂marginalRef i)-(∫ t,u i t ∂marginalRef i))) := by
  have ix : Integrable (fun z => (Q.ν z:ℝ)*(l+∑ i : Fin 4,v i (coord i z))) cuadrado := by
    simp_rw [mul_add,Finset.mul_sum]
    exact (Q.masaFinita.mul_const l).add (integrable_finset_sum _ (fun i _ => hq.ocupada i))
  have area:=tangente_integrada cuadrado (fun z => (P.ν z:ℝ)) (fun z => (Q.ν z:ℝ)) _ P.masaFinita Q.masaFinita ix
    ent.1 pos (Eventually.of_forall (fun z => NNReal.coe_nonneg _)) euler
  rw [integrar_campo_del_tablero Q hq l] at area
  change Q.rho+(Q.rho*l+_)-P.rho≤_ at area
  have line (i : Fin 4) :
      (∫ t,Q.u i t ∂marginalRef i)-(∫ t,u i t ∂marginalRef i)+(∫ t,Q.u i t*v i t ∂marginalRef i)≤
        ∫ t,xlogx (Q.u i t) ∂marginalRef i := by
    have b:=tangente_integrada _ _ _ _ (ui i) (Q.u_integrable i) (hq.libre i) (ent.2 i) (up i)
      ((Q.admisible i).mono (fun t ht => sub_nonneg.mpr ht)) (eq i)
    linarith only [b]
  have lines:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => line i)
  rw [Finset.sum_add_distrib] at lines
  rw [←complementar_campo Q hq]
  change -3*Q.rho-_-_≤_
  linarith only [area,lines]

theorem referencia_reescalada {p κ M L} (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L)
    (x : ℝ≥0) (xp : 0<x) (i : Fin 4) :
    Integrable (holguraLinea p x i) (marginalRef i) ∧
    (∀ᵐ t ∂marginalRef i,0<holguraLinea p x i t) ∧
    (∀ᵐ t ∂marginalRef i,Real.log (holguraLinea p x i t)=campoPerfil p x i t) := by
  have base : ContinuousOn (fun t => (factorF p i t:ℝ)) (rangoF i) :=
    continua_de_cota lp (regular_familia sp i).oscilacion
  have I : IntegrableOn (fun t => (factorF p i t:ℝ)) (Ioc (extremoIzq i) (extremoDer i)) volume :=
    (base.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have m : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
  have u := I.const_mul (if i.val<2 then (x:ℝ) else 1)
  have both : ∀ᵐ t ∂marginalRef i,0<holguraLinea p x i t ∧ Real.log (holguraLinea p x i t)=campoPerfil p x i t := by
    filter_upwards [linea_en_dominio i] with t ht
    rw [holguraLinea,campoPerfil,recorte_fijo i ht,correccionRC]
    have pf := kp.trans_le ((regular_familia sp i).minimo _ ht)
    by_cases rc : i.val<2
    · have xr : 0<(x:ℝ) := by exact_mod_cast xp
      simp [rc,mul_pos xr pf,Real.log_mul xr.ne' pf.ne']
    · simp [rc,pf]
  exact ⟨by rw [m]; exact u,both.mono (fun _ h => h.1),both.mono (fun _ h => h.2)⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_dual_con_referencias
#print axioms ArticuloA.Historias.referencia_reescalada
