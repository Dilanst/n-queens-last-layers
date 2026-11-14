import IdentificacionDelPerfilFisico
open Set MeasureTheory Filter
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem entropias_del_optimo_integrables {P p x b κ M L} (h : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) :
    Integrable (fun z => xlogx (P.ν z)) cuadrado ∧
    ∀ i,Integrable (fun z => xlogx (P.u i z)) (marginalRef i) := by
  let f:=campoPerfil p (escalaLog x)
  let l:=Real.log (b/(escalaLog x:ℝ)^2)
  have cf:=campo_perfil_integrable P sp kp lp (escalaLog x)
  have sum : Integrable (fun z => (P.ν z:ℝ)*(l+∑ i : Fin 4,f i (coord i z))) cuadrado := by
    simp_rw [mul_add,Finset.mul_sum]
    exact (P.masaFinita.mul_const _).add (integrable_finset_sum _ (fun i _ => cf.ocupada i))
  constructor
  · apply sum.congr
    filter_upwards [log_de_densidad_fisica h sp kp] with z hz
    exact congrArg (fun r => (P.ν z:ℝ)*r) hz.symm
  · intro i
    exact (cf.libre i).congr ((holgura_por_campo h sp kp i).mono (fun _ q => q.symm))

theorem soporte_del_perfil_positivo {P p x b κ M L} (h : EulerFisica P p x b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (lp : 0≤L) (xp : 0<x) (Q : TableroMedido)
    (qi : Integrable (fun z => xlogx (Q.ν z)) cuadrado)
    (ui : ∀ i,Integrable (fun z => xlogx (Q.u i z)) (marginalRef i)) :
    Q.s-P.s≤ -(Q.rho-P.rho)*Real.log (b/(x:ℝ)^2) := by
  have pos : ∀ᵐ z ∂cuadrado,0<(P.ν z:ℝ) := by
    filter_upwards [h.real,tablero_en_dominio] with z eq mem
    rw [eq]
    exact mul_pos h.coef ((pow_pos kp 4).trans_le (limites_del_producto sp kp.le _ _ mem.1 mem.2).1)
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have each (i : Fin 4) : ∀ᵐ t ∂marginalRef i,0<P.u i t ∧ Real.log (P.u i t)=campoPerfil p x i t := by
    filter_upwards [h.linea i,linea_en_dominio i] with t eq mem
    have posf := kp.trans_le ((regular_familia sp i).minimo _ mem)
    rw [eq,holguraLinea,campoPerfil,recorte_fijo i mem,correccionRC]
    by_cases rc : i.val<2
    · simp only [if_pos rc,Real.log_mul xr.ne' posf.ne']; exact ⟨mul_pos xr posf,trivial⟩
    · simp [rc,posf]
  exact soporte_variacional P Q (campo_perfil_integrable P sp kp lp x) (campo_perfil_integrable Q sp kp lp x)
    _ pos (fun i => (each i).mono (fun _ ht => ht.1))
    (by simpa only [escalaLog,if_neg xp.ne'] using log_de_densidad_fisica h sp kp)
    (fun i => (each i).mono (fun _ ht => ht.2)) qi ui

theorem soporte_entre_perfiles {P Q p v x y a b κ M L} (hx : EulerFisica Q v x a) (hy : EulerFisica P p y b)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial v κ M L) (kp : 0<κ) (lp : 0≤L) (yp : 0<y) :
    Q.s-P.s≤((x:ℝ)-(y:ℝ))*Real.log (b/(y:ℝ)^2) := by
  obtain ⟨i,j⟩:=entropias_del_optimo_integrables hx sq kp lp
  have h:=soporte_del_perfil_positivo hy sp kp lp yp Q i j
  rw [hx.masa,hy.masa] at h
  convert h using 1; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.soporte_del_perfil_positivo
#print axioms ArticuloA.Historias.soporte_entre_perfiles
