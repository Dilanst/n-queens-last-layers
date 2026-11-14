import CampoLogaritmicoDelOptimo
open Set MeasureTheory Filter
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

def escalaLog (x : ℝ≥0) := if x=0 then 1 else x
theorem escala_pos (x : ℝ≥0) : 0<escalaLog x := by
  unfold escalaLog; split_ifs with hx
  · exact zero_lt_one
  · exact lt_of_le_of_ne x.property (Ne.symm hx)

def holguraLinea (p : FactoresContinuos) (x : ℝ≥0) (i : Fin 4) (s : ℝ) : ℝ :=
  (if i.val<2 then (x:ℝ) else 1)*(factorF p i s:ℝ)

structure EulerFisica (P : TableroMedido) (p : FactoresContinuos) (x : ℝ≥0) (b : ℝ) : Prop where
  coef : 0<b
  masa : P.rho=1-(x:ℝ)
  real : ∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=b*pesoContinuo p z.1 z.2
  linea : ∀ i,∀ᵐ s ∂marginalRef i,P.u i s=holguraLinea p x i s

theorem tablero_en_dominio : ∀ᵐ z ∂cuadrado,z.1∈unidadCerrada ∧ z.2∈unidadCerrada := by
  have one : ∀ᵐ t ∂unidad,t∈unidadCerrada := ae_restrict_mem measurableSet_Icc
  apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Icc |>.inter (measurable_snd measurableSet_Icc))).mpr
  filter_upwards [one] with x hx
  exact one.mono (fun _ hy => ⟨hx,hy⟩)

theorem linea_en_dominio (i : Fin 4) : ∀ᵐ s ∂marginalRef i,s∈rangoF i := by
  have e : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
  rw [e]
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ ht => ⟨ht.1.le,ht.2⟩)

theorem coordenadas_en_dominio {z : ℝ×ℝ} (h : z.1∈unidadCerrada ∧ z.2∈unidadCerrada) :
    ∀ i,coord i z∈rangoF i := by
  obtain ⟨d,a⟩:=dominios _ _ h.1 h.2
  intro i; fin_cases i; exacts [h.1,h.2,d,a]

theorem log_de_densidad_fisica {P p x b κ M L} (h : EulerFisica P p x b) (data : ControlEspacial p κ M L)
    (kp : 0<κ) :
    ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=Real.log (b/(escalaLog x:ℝ)^2)+
      ∑ i : Fin 4,campoPerfil p (escalaLog x) i (coord i z) := by
  filter_upwards [h.real,tablero_en_dominio] with z eq hz
  let v:=fun i => (factorF p i (coord i z):ℝ)
  have pos (i) : 0<v i := kp.trans_le ((regular_familia data i).minimo _ (coordenadas_en_dominio hz i))
  have dec:=log_del_producto (y:=v) h.coef pos (show (P.ν z:ℝ)=b*v 0*v 1*v 2*v 3 by rw [eq]; dsimp [v,pesoContinuo,factorF,coord]; ring)
  have ep : 0<(escalaLog x:ℝ) := by exact_mod_cast escala_pos x
  have add (i) : campoPerfil p (escalaLog x) i (coord i z)=correccionRC (escalaLog x) i+Real.log (v i) := by
    simp only [campoPerfil,recorte_fijo i (coordenadas_en_dominio hz i),v]
  rw [dec,Real.log_div h.coef.ne' (pow_ne_zero 2 ep.ne'),Real.log_pow]
  simp_rw [add,Finset.sum_add_distrib]
  have total : (∑ i : Fin 4,correccionRC (escalaLog x) i)=2*Real.log (escalaLog x) := by
    rw [Fin.sum_univ_four]; norm_num [correccionRC,show ¬(3:Fin 4).val<2 by decide]; ring
  rw [total]; ring

theorem holgura_por_campo {P p x b κ M L} (h : EulerFisica P p x b) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (i : Fin 4) :
    ∀ᵐ s ∂marginalRef i,xlogx (P.u i s)=P.u i s*campoPerfil p (escalaLog x) i s := by
  filter_upwards [h.linea i,linea_en_dominio i] with s eq hs
  have pos:=kp.trans_le ((regular_familia data i).minimo _ hs)
  rw [eq,holguraLinea,campoPerfil,recorte_fijo i hs,correccionRC]
  by_cases rc : i.val<2
  · by_cases hx : x=0
    · simp [rc,hx,xlogx]
    · have xr : (x:ℝ)≠0 := by exact_mod_cast hx
      simp [rc,escalaLog,hx,xlogx,Real.log_mul xr pos.ne']
  · simp [rc,xlogx]

theorem entropia_fisica {P p x b κ M L} (h : EulerFisica P p x b) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (lp : 0≤L) :
    P.s=P.rho*(-Real.log (b/(escalaLog x:ℝ)^2)-3)-entropiaDeFactores p (escalaLog x) := by
  rw [←integral_del_campo data kp lp]
  exact valor_de_euler P (campo_perfil_integrable P data kp lp _) _ (log_de_densidad_fisica h data kp)
    (holgura_por_campo h data kp)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_fisica
