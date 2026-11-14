import TangenteConReferenciasAuxiliares
open Set MeasureTheory Filter
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem log_lleno_con_escala_auxiliar {P p b κ M L} (h : EulerFisica P p 0 b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (x : ℝ≥0) (xp : 0<x) :
    ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=Real.log (b/(x:ℝ)^2)+∑ i : Fin 4,campoPerfil p x i (coord i z) := by
  have xr : (x:ℝ)≠0 := by exact_mod_cast xp.ne'
  filter_upwards [log_de_densidad_fisica h sp kp] with z eq
  rw [eq,Real.log_div h.coef.ne' (pow_ne_zero 2 xr),Real.log_pow,Fin.sum_univ_four,Fin.sum_univ_four]
  norm_num [escalaLog,campoPerfil,correccionRC,show ¬(3:Fin 4).val<2 by decide]
  ring

theorem masas_de_referencia {P Q p v x b a} (full : EulerFisica P p 0 b) (part : EulerFisica Q v x a)
    (R : (∫ t in (0:ℝ)..1,(p.fila t:ℝ))=1) (C : (∫ t in (0:ℝ)..1,(p.columna t:ℝ))=1)
    (i : Fin 4) : (∫ t,Q.u i t ∂marginalRef i)-(∫ t,holguraLinea p x i t ∂marginalRef i)=
      if i.val<2 then 0 else (x:ℝ) := by
  have qmass : Q.rho=1-(x:ℝ) := part.masa
  have pmass : P.rho=1 := by simpa using full.masa
  by_cases rc : i.val<2
  · rw [if_pos rc]
    have q : (∫ t,Q.u i t ∂marginalRef i)=(x:ℝ) := by
      have d:=desplazamiento_de_vacancia P Q i
      have zero:=integral_eq_zero_of_ae (vacancia_transversal_llena full i rc)
      rw [pmass,qmass,zero] at d; linarith only [d]
    have factor : (∫ t,(factorF p i t:ℝ) ∂marginalRef i)=1 := by
      rw [intervalIntegral.integral_of_le zero_le_one] at R C
      fin_cases i
      · exact R
      · exact C
      · exact False.elim ((by decide : ¬(2:Fin 4).val<2) rc)
      · exact False.elim ((by decide : ¬(3:Fin 4).val<2) rc)
    simp [holguraLinea,rc,integral_const_mul,factor,q]
  · rw [if_neg rc]
    have eq : P.u i=ᵐ[marginalRef i] holguraLinea p x i := (full.linea i).mono
      (fun t ht => by simpa [holguraLinea,rc] using ht)
    rw [←integral_congr_ae eq,desplazamiento_de_vacancia,pmass,qmass]; ring

theorem cota_superior_desde_el_lleno {P Q p v x b a κ M L} (full : EulerFisica P p 0 b)
    (part : EulerFisica Q v x a) (sp : ControlEspacial p κ M L) (sv : ControlEspacial v κ M L)
    (kp : 0<κ) (lp : 0≤L) (xp : 0<x)
    (R : (∫ t in (0:ℝ)..1,(p.fila t:ℝ))=1) (C : (∫ t in (0:ℝ)..1,(p.columna t:ℝ))=1) :
    Q.s-P.s≤(x:ℝ)*(2+Real.log b-2*Real.log x) := by
  have pos : ∀ᵐ z ∂cuadrado,0<(P.ν z:ℝ) := by
    filter_upwards [full.real,tablero_en_dominio] with z e mem
    rw [e]; exact mul_pos full.coef ((pow_pos kp 4).trans_le (limites_del_producto sp kp.le _ _ mem.1 mem.2).1)
  have ref:=referencia_reescalada sp kp lp x xp
  have du:=cota_dual_con_referencias P Q (holguraLinea p x) (campoPerfil p x) _ (campo_perfil_integrable Q sp kp lp x)
    pos (log_lleno_con_escala_auxiliar full sp kp x xp) (fun i => (ref i).1)
    (fun i => (ref i).2.1) (fun i => (ref i).2.2) (entropias_del_optimo_integrables part sv kp lp)
  have pmass : P.rho=1 := by simpa using full.masa
  have xr : (x:ℝ)≠0 := by exact_mod_cast xp.ne'
  rw [pmass,part.masa,integral_del_campo sp kp lp,Real.log_div full.coef.ne' (pow_ne_zero 2 xr),Real.log_pow] at du
  simp_rw [masas_de_referencia full part R C] at du
  rw [Fin.sum_univ_four] at du
  have vfull:=entropia_sin_logaritmos_singulares full sp kp lp
  rw [vfull]
  norm_num [show ¬(3:Fin 4).val<2 by decide,entropiaDeFactores] at du ⊢
  linarith only [du]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_superior_desde_el_lleno
