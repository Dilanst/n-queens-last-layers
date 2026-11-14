import CamposNormalizadosParaLaTraslacion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def filaExteriorB33 (p : FactoresContinuos) (x b : ℝ) :=
  filaPorEuler (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) x b
def densidadExteriorB33 (p : FactoresContinuos) (x b : ℝ) (z : ℝ×ℝ) :=
  b*filaExteriorB33 p x b z.1*campoR15 p 1 z.2*campoR15 p 2 (z.1-z.2)*campoR15 p 3 (z.1+z.2)

theorem cavidad_fila_en_el_dominio (p : FactoresContinuos) {s : ℝ} (hs : s∈unidadCerrada) :
    integralFisica p 0 s=(p.fila s:ℝ)*nucleoFilaExtendida (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) s := by
  unfold nucleoFilaExtendida; rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro c hc; rw [uIcc_of_le zero_le_one] at hc
  dsimp only
  obtain ⟨d,a⟩:=dominios s c hs hc
  rw [campo_dentro_de_su_intervalo p 1 hc,campo_dentro_de_su_intervalo p 2 d,campo_dentro_de_su_intervalo p 3 a]
  dsimp [pesoContinuo,camposFisicos,factorF]; ring

theorem fila_por_euler_coincide_en_el_tablero {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    {s : ℝ} (hs : s∈unidadCerrada) : filaExteriorB33 p x b s=p.fila s := by
  have e:=h.euler 0 s hs
  rw [cavidad_fila_en_el_dominio p hs] at e
  change b*((p.fila s:ℝ)*_)+x*(p.fila s:ℝ)=1 at e
  let j:=nucleoFilaExtendida (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) s
  have a : (p.fila s:ℝ)*(x+b*j)=1 := by dsimp [j]; linarith only [e]
  exact (eq_inv_of_mul_eq_one_left a).symm

theorem densidad_exterior_en_el_cuadrado {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    densidadExteriorB33 p x b (r,c)=b*pesoContinuo p r c := by
  obtain ⟨d,a⟩:=dominios r c hr hc
  unfold densidadExteriorB33
  rw [fila_por_euler_coincide_en_el_tablero h hr,campo_dentro_de_su_intervalo p 1 hc,
    campo_dentro_de_su_intervalo p 2 d,campo_dentro_de_su_intervalo p 3 a]
  dsimp [camposFisicos,factorF,pesoContinuo]; ring

theorem soporte_de_densidad_extendida {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) :
    Continuous (densidadExteriorB33 p x b) ∧ ∀ r,∀ c∈unidadCerrada,
      |densidadExteriorB33 p x b (r,c)|≤b*(1/(x+b*κ^2))*M := by
  have R:=nucleo_y_fila_del_perfil h xn bp kp
  have cc:=campo_continuo_por_recorte h.continuos
  refine ⟨(((continuous_const.mul (R.1.comp continuous_fst)).mul ((cc 1).comp continuous_snd)).mul
    ((cc 2).comp (continuous_fst.sub continuous_snd))).mul ((cc 3).comp (continuous_fst.add continuous_snd)),?_⟩
  intro r c hc
  let v:=b*filaExteriorB33 p x b r*campoR15 p 1 c
  have rp : 0≤filaExteriorB33 p x b r := (one_div_nonneg.mpr (add_nonneg xn bp.le)).trans (R.2 r).1
  have cpos : 0≤campoR15 p 1 c := NNReal.coe_nonneg _
  have vp : 0≤v := mul_nonneg (mul_nonneg bp.le rp) cpos
  have d:=h.diagonal 2 (by decide) _ (recorte_dentro 2 (r-c))
  have a:=h.diagonal 3 (by decide) _ (recorte_dentro 3 (r+c))
  change κ≤campoR15 p 2 (r-c) ∧ campoR15 p 2 (r-c)≤1 at d
  change κ≤campoR15 p 3 (r+c) ∧ campoR15 p 3 (r+c)≤1 at a
  have cm : campoR15 p 1 c≤M := (campo_dentro_de_su_intervalo p 1 hc).le.trans (h.columna c hc)
  change |v*campoR15 p 2 (r-c)*campoR15 p 3 (r+c)|≤_
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg vp (kp.le.trans d.1)) (kp.le.trans a.1))]
  have d1:=mul_le_of_le_one_right vp d.2
  have a1:=mul_le_of_le_one_right (mul_nonneg vp (kp.le.trans d.1)) a.2
  exact a1.trans (d1.trans (mul_le_mul (mul_le_mul_of_nonneg_left (R.2 r).2.1 bp.le) cm cpos
    (mul_nonneg bp.le (rp.trans (R.2 r).2.1))))

theorem ecuacion_de_la_fila_en_toda_la_recta {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (r : ℝ) :
    (∫ c in (0:ℝ)..1,densidadExteriorB33 p x b (r,c))+x*filaExteriorB33 p x b r=1 := by
  have esc : (∫ c in (0:ℝ)..1,densidadExteriorB33 p x b (r,c))=
      (b*filaExteriorB33 p x b r)*nucleoFilaExtendida (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) r := by
    unfold nucleoFilaExtendida; rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro c _; unfold densidadExteriorB33; ring
  rw [esc]
  have a:=((nucleo_y_fila_del_perfil h xn bp kp).2 r).2.2
  change filaExteriorB33 p x b r*(x+b*_)=1 at a
  linarith only [a]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cavidad_fila_en_el_dominio
#print axioms ArticuloA.Historias.fila_por_euler_coincide_en_el_tablero
#print axioms ArticuloA.Historias.densidad_exterior_en_el_cuadrado
#print axioms ArticuloA.Historias.soporte_de_densidad_extendida
#print axioms ArticuloA.Historias.ecuacion_de_la_fila_en_toda_la_recta
