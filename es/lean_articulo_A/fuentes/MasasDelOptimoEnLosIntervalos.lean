import SoporteDelValorDenso
import UnaCotaParaTodasLasCapas
import Mathlib.MeasureTheory.Integral.Prod
open Set MeasureTheory Filter
open scoped BigOperators NNReal Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem integral_de_area_igual_a_iterada (v : ℝ→ℝ→ℝ) (iv : Integrable (fun z : ℝ×ℝ => v z.1 z.2) cuadrado) :
    (∫ z,v z.1 z.2 ∂cuadrado)=integralTablero v := by
  letI : IsFiniteMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  rw [cuadrado,integral_prod _ iv]
  unfold unidad integralTablero integralFila
  simp only [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]

theorem integral_masa_cuadrada {P p x b} (h : EulerFisica P p x b) :
    integralTablero (pesoContinuo p)=P.rho/b := by
  let F:=fun z : ℝ×ℝ => pesoContinuo p z.1 z.2
  have eq : (fun z => (P.ν z:ℝ)/b) =ᵐ[cuadrado] F := h.real.mono
    (fun z hz => by dsimp [F]; rw [hz,mul_div_cancel_left₀ _ h.coef.ne'])
  have integrable : Integrable F cuadrado := (P.masaFinita.div_const b).congr eq
  rw [← integral_de_area_igual_a_iterada _ integrable]
  change (∫ z,F z ∂cuadrado)=_
  rw [←integral_congr_ae eq,integral_div]
  rfl

theorem medida_linea_oblicua (i : Fin 4) (ob : 2 ≤ i.val) :
    (∫ _ : ℝ,(1:ℝ) ∂marginalRef i)=2 := by
  fin_cases i
  · exact False.elim ((by decide : ¬2 ≤ (0:Fin 4).val) ob)
  · exact False.elim ((by decide : ¬2 ≤ (1:Fin 4).val) ob)
  · norm_num [marginalRef,integral_const,Real.volume_Ioc]
  · norm_num [marginalRef,integral_const,Real.volume_Ioc]

theorem masa_holgura_oblicua {P p x b} (h : EulerFisica P p x b) (i : Fin 4) (ob : 2 ≤ i.val) :
    (∫ t,(factorF p i t:ℝ) ∂marginalRef i)=2-P.rho := by
  have eq : (P.u i)=ᵐ[marginalRef i] fun t => (factorF p i t:ℝ) := by
    filter_upwards [h.linea i] with t ht
    simpa [holguraLinea,not_lt.mpr ob] using ht
  rw [←integral_congr_ae eq]
  unfold TableroMedido.u
  rw [integral_sub (integrable_const _) (P.m_integrable i),medida_linea_oblicua i ob,masa_de_cada_linea P.ley i]
  rfl

theorem datos_de_cuadratura {n h : ℕ} (hn : 0<n) (size : 2*h≤n) {P p b κ M L B}
    (src : EulerFisica P p (fraccionHuecos n h) b) (sp : ControlEspacial p κ M L) (kp : 0<κ)
    (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L) (bb : b≤B)
    (de : p.diagonal (-1)=1) (ae : p.anti 0=1)
    (r : (∫ t in (0:ℝ)..1,(p.fila t:ℝ))=1) (c : (∫ t in (0:ℝ)..1,(p.columna t:ℝ))=1) :
    PerfilKL n h p κ M L b (1/(2*B)) := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have Bp:=src.coef.trans_le bb
  have nh : h≤n := by omega
  have fr : (fraccionHuecos n h:ℝ)=(h:ℝ)/n := by simp [fraccionHuecos]
  have rho : P.rho=1-(h:ℝ)/n := by rw [src.masa,fr]
  have half : (1:ℝ)/2≤P.rho := by
    have d : (h:ℝ)/n≤1/2 := (div_le_iff₀ np).mpr (by
      have q : 2*(h:ℝ)≤n := by exact_mod_cast size
      linarith)
    rw [rho]; linarith
  have scaled (i : Fin 4) (hi : 2 ≤ i.val) : (n:ℝ)*(∫ t,(factorF p i t:ℝ) ∂marginalRef i)=(n:ℝ)+h := by
    rw [masa_holgura_oblicua src i hi,rho]; field_simp; ring
  refine ⟨sp,kp,k1,m1,lp,src.coef,by positivity,de,ae,r,c,?_,?_,?_,?_⟩
  · rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]; exact scaled 2 (by decide)
  · rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2)]; exact scaled 3 (by decide)
  · rw [integral_masa_cuadrada src,rho,Nat.cast_sub nh]; field_simp
  · rw [integral_masa_cuadrada src]
    have cmp := mul_le_mul_of_nonneg_left bb (show 0≤(1:ℝ)/2 by norm_num)
    apply (div_le_div_iff₀ (by positivity : 0<2*B) src.coef).mpr
    have u:=mul_le_mul_of_nonneg_right half Bp.le
    linarith
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_masa_cuadrada
#print axioms ArticuloA.Historias.datos_de_cuadratura
