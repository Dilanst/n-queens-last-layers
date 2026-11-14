import CotaPositivaDeLasUltimasCapas
open Set
open scoped NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

def factoresDelCruce (p : FactoresContinuos) (r c i j : ℝ) : Fin 4→ℝ
  | 0 => p.diagonal (r-j)
  | 1 => p.anti (r+j)
  | 2 => p.diagonal (i-c)
  | 3 => p.anti (i+c)

def factorDelCruce (p : FactoresContinuos) (r c i j : ℝ) : ℝ :=
  let v:=factoresDelCruce p r c i j
  v 0*v 1*v 2*v 3

def integrandoDirecto (p : FactoresContinuos) (r c i j : ℝ) : ℝ :=
  pesoContinuo p i j*factorDelCruce p r c i j

theorem rango_de_holguras {p κ M L} (sp : ControlEspacial p κ M L) {r c i j : ℝ}
    (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada) (hj : j∈unidadCerrada) :
    ∀ t,|factoresDelCruce p r c i j t|≤M := by
  obtain ⟨d,a⟩:=dominios _ _ hr hj
  obtain ⟨d',a'⟩:=dominios _ _ hi hc
  intro t; fin_cases t <;> simp only [factoresDelCruce,abs_of_nonneg (NNReal.coe_nonneg _)]
  exacts [sp.Dmax _ d,sp.Amax _ a,sp.Dmax _ d',sp.Amax _ a']

theorem variacion_del_factor_directo {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L)
    {r c i j u v : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada)
    (hj : j∈unidadCerrada) (hu : u∈unidadCerrada) (hv : v∈unidadCerrada) :
    |factorDelCruce p r c i j-factorDelCruce p r c u v|≤4*M^3*L*(|i-u|+|j-v|) := by
  have first:=dominios _ _ hr hj
  have first':=dominios _ _ hr hv
  have sec:=dominios _ _ hi hc
  have sec':=dominios _ _ hu hc
  have dx : L*|i-u|≤L*(|i-u|+|j-v|) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) lp
  have dy : L*|j-v|≤L*(|i-u|+|j-v|) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) lp
  have dif (t : Fin 4) : |factoresDelCruce p r c i j t-factoresDelCruce p r c u v t|≤L*(|i-u|+|j-v|) := by
    fin_cases t
    · apply (sp.D.oscilacion _ first.1 _ first'.1).trans
      rwa [show r-j-(r-v)= -(j-v) by ring,abs_neg]
    · apply (sp.A.oscilacion _ first.2 _ first'.2).trans
      rwa [show r+j-(r+v)=j-v by ring]
    · apply (sp.D.oscilacion _ sec.1 _ sec'.1).trans
      rwa [show i-c-(u-c)=i-u by ring]
    · apply (sp.A.oscilacion _ sec.2 _ sec'.2).trans
      rwa [show i+c-(u+c)=i-u by ring]
  exact (cuatro_factores _ _ M _ (rango_de_holguras sp hr hc hi hj)
    (rango_de_holguras sp hr hc hu hv) dif).trans_eq (by ring)

theorem factor_acotado {p κ M L} (sp : ControlEspacial p κ M L)
    {r c i j : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada) (hj : j∈unidadCerrada) :
    |factorDelCruce p r c i j|≤M^4 := by
  have cap:=rango_de_holguras sp hr hc hi hj
  have mp : 0≤M := (abs_nonneg _).trans (cap 0)
  unfold factorDelCruce; simp only [abs_mul]
  calc _ ≤ M*M*M*M := mul_le_mul (mul_le_mul (mul_le_mul (cap 0) (cap 1) (abs_nonneg _) mp)
        (cap 2) (abs_nonneg _) (by positivity)) (cap 3) (abs_nonneg _) (by positivity)
       _ = _ := by ring

theorem oscilacion_del_integrando {p κ M L} (sp : ControlEspacial p κ M L) (kp : 0≤κ) (lp : 0≤L)
    {r c i j u v : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (hi : i∈unidadCerrada)
    (hj : j∈unidadCerrada) (hu : u∈unidadCerrada) (hv : v∈unidadCerrada) :
    |integrandoDirecto p r c i j-integrandoDirecto p r c u v|≤8*M^7*L*(|i-u|+|j-v|) := by
  let w:=pesoContinuo p
  let f:=factorDelCruce p r c
  have capw : |w i j|≤M^4 := by
    have cap:=limites_del_producto sp kp i j hi hj
    exact (abs_of_nonneg ((pow_nonneg kp 4).trans cap.1)).le.trans cap.2
  have capf:=factor_acotado sp hr hc hu hv
  have dw:=variacion_del_peso sp lp i u j v hi hu hj hv
  have df:=variacion_del_factor_directo sp lp hr hc hi hj hu hv
  change |w i j*f i j-w u v*f u v|≤_
  rw [show w i j*f i j-w u v*f u v=w i j*(f i j-f u v)+f u v*(w i j-w u v) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact (add_le_add (mul_le_mul capw df (abs_nonneg _) (by positivity))
    (mul_le_mul capf dw (abs_nonneg _) (by positivity))).trans_eq (by ring)

theorem cuadratura_del_integrando_directo {p κ M L} (sp : ControlEspacial p κ M L) (kp : 0≤κ) (lp : 0≤L)
    {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) (n : ℕ) (np : 0<n) :
    |(n:ℝ)^2*integralTablero (integrandoDirecto p r c)-muestraTablero n (integrandoDirecto p r c)|≤
      2*(8*M^7*L)*n := by
  have mp : 0≤M := (NNReal.coe_nonneg _).trans (sp.Rmax _ hr)
  apply cuadratura_dos_dimensiones n np _ _ (by positivity)
  · intro i hi u hu j hj; simpa using oscilacion_del_integrando sp kp lp hr hc hi hj hu hj
  · intro i hi j hj v hv; simpa using oscilacion_del_integrando sp kp lp hr hc hi hj hi hv
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuadratura_del_integrando_directo
