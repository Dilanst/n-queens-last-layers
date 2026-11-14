import IntegrandoDeLaReparacionDirecta
open Set
namespace ArticuloA.Historias
open Perfil
noncomputable section

def CercaniaDeFactores (p q : FactoresContinuos) (d : ℝ) : Prop :=
  ∀ (i : Fin 4),∀ t∈rangoF i,|(factorF p i t:ℝ)-factorF q i t|≤d

private theorem techo_de_cada_factor {p κ M L} (sp : ControlEspacial p κ M L) (i : Fin 4) (t : ℝ) (ht : t∈rangoF i) :
    |(factorF p i t:ℝ)|≤M := by
  rw [abs_of_nonneg (NNReal.coe_nonneg _)]
  fin_cases i; exacts [sp.Rmax _ ht,sp.Cmax _ ht,sp.Dmax _ ht,sp.Amax _ ht]

theorem cambia_el_integrando {p q κ M L d} (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L)
    (kp : 0≤κ) (close : CercaniaDeFactores p q d)
    {r c i j : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada) (hj : j∈unidadCerrada) :
    |integrandoDirecto p r c i j-integrandoDirecto q r c i j|≤8*M^7*d := by
  let src (P : FactoresContinuos) := fun t : Fin 4 => (factorF P t (coord t (i,j)):ℝ)
  have domain:=coordenadas_en_dominio (z:=(i,j)) ⟨hi,hj⟩
  have dw : |pesoContinuo p i j-pesoContinuo q i j|≤4*M^3*d :=
    cuatro_factores (src p) (src q) _ _ (fun t => techo_de_cada_factor sp _ _ (domain t))
      (fun t => techo_de_cada_factor sq _ _ (domain t)) (fun t => close t _ (domain t))
  have dist (t : Fin 4) : |factoresDelCruce p r c i j t-factoresDelCruce q r c i j t|≤d := by
    have rc:=dominios _ _ hr hj
    have ic:=dominios _ _ hi hc
    fin_cases t
    · exact close 2 _ rc.1
    · exact close 3 _ rc.2
    · exact close 2 _ ic.1
    · exact close 3 _ ic.2
  have df:=cuatro_factores _ _ M d (rango_de_holguras sp hr hc hi hj) (rango_de_holguras sq hr hc hi hj) dist
  change |factorDelCruce p r c i j-factorDelCruce q r c i j|≤_ at df
  let w:=fun P => pesoContinuo P i j
  let f:=fun P => factorDelCruce P r c i j
  have cp : |w p|≤M^4 := by
    have bounds:=limites_del_producto sp kp _ _ hi hj
    exact (abs_of_nonneg ((pow_nonneg kp 4).trans bounds.1)).le.trans bounds.2
  change |w p*f p-w q*f q|≤_
  rw [show w p*f p-w q*f q=w p*(f p-f q)+f q*(w p-w q) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact (add_le_add (mul_le_mul cp df (abs_nonneg _) (by positivity))
    (mul_le_mul (factor_acotado sq hr hc hi hj) dw (abs_nonneg _) (by positivity))).trans_eq (by ring)

theorem cambio_con_coeficiente {p q κ M L d b v} (sp : ControlEspacial p κ M L)
    (sq : ControlEspacial q κ M L) (kp : 0≤κ) (bp : 0≤b) (close : CercaniaDeFactores p q d)
    {r c i j : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada) (hj : j∈unidadCerrada) :
    |b*integrandoDirecto p r c i j-v*integrandoDirecto q r c i j|≤b*(8*M^7*d)+M^8*|b-v| := by
  let J:=fun P => integrandoDirecto P r c i j
  have cap : |J q|≤M^8 := by
    have bounds:=limites_del_producto sq kp _ _ hi hj
    change |pesoContinuo q i j*factorDelCruce q r c i j|≤_
    rw [abs_mul,abs_of_nonneg ((pow_nonneg kp 4).trans bounds.1)]
    exact (mul_le_mul bounds.2 (factor_acotado sq hr hc hi hj) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  change |b*J p-v*J q|≤_
  rw [show b*J p-v*J q=b*(J p-J q)+J q*(b-v) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_of_nonneg bp]
  exact add_le_add (mul_le_mul_of_nonneg_left (cambia_el_integrando sp sq kp close hr hc hi hj) bp)
    (mul_le_mul_of_nonneg_right cap (abs_nonneg _))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cambio_con_coeficiente
