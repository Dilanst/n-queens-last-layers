import CompararDosPerfilesPorSuCuadratura
import NucleoInversoDelPerfil
open Filter Set MeasureTheory
open scoped NNReal Interval Topology BigOperators
namespace ArticuloA.Historias
open Perfil
noncomputable section

def psiDiagonal (p : FactoresContinuos) (r c : ℝ) := (p.diagonal (r-c):ℝ)*p.anti (r+c)
def gammaDelPerfil (p : FactoresContinuos) (b r c : ℝ) :=
  integralTablero (fun i j => (b*pesoContinuo p r j)*(b*pesoContinuo p i c)*psiDiagonal p i j)

private theorem extrae_escalar (b : ℝ) (f : ℝ→ℝ→ℝ) :
    integralTablero (fun i j => b*f i j)=b*integralTablero f := by
  unfold integralTablero integralFila; simp_rw [intervalIntegral.integral_const_mul]

theorem gamma_en_el_cuadrado (p : FactoresContinuos) (b r c : ℝ) :
    gammaDelPerfil p b r c=b*(p.fila r:ℝ)*(p.columna c:ℝ)*perfilDirectoContinuo p b r c := by
  let J:=fun (f : ℝ×ℝ→ℝ) => integralTablero (fun i j => f (i,j))
  have eq:=factor_inverso J (fun a f => extrae_escalar a (fun i j => f (i,j))) b
    (fun t => (p.fila t:ℝ)) (fun t => (p.columna t:ℝ)) (psiDiagonal p) (fun i j => b*pesoContinuo p i j)
    (by intro i j; unfold pesoContinuo psiDiagonal; ring) r c
  have arg : (fun i j => (b*pesoContinuo p i j)*psiDiagonal p r j*psiDiagonal p i c)=
      (fun i j => b*integrandoDirecto p r c i j) := by
    funext i j; unfold integrandoDirecto factorDelCruce factoresDelCruce psiDiagonal; ring
  unfold gammaDelPerfil perfilDirectoContinuo
  convert eq using 1
  dsimp only [J]; rw [arg,extrae_escalar]

theorem piso_integral_del_cruce {p κ M L b} (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) (bp : 0<b)
    {r c : ℝ} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    b*κ^8≤perfilDirectoContinuo p b r c := by
  let A:=perfilDirectoContinuo p b r c
  let D:=b*(16*M^7*L)
  have one {i j : ℝ} (hi : i∈unidadCerrada) (hj : j∈unidadCerrada) : κ^8 ≤ integrandoDirecto p r c i j := by
    have h₁:=dominios r j hr hj
    have h₂:=dominios i c hi hc
    have lower (t : Fin 4) : κ≤factoresDelCruce p r c i j t := by
      fin_cases t; exacts [sp.D.minimo _ h₁.1,sp.A.minimo _ h₁.2,sp.D.minimo _ h₂.1,sp.A.minimo _ h₂.2]
    have min : κ*κ*κ*κ≤factorDelCruce p r c i j :=
      mul_le_mul (mul_le_mul (mul_le_mul (lower 0) (lower 1) kp.le (kp.le.trans (lower 0)))
        (lower 2) kp.le (mul_nonneg (kp.le.trans (lower 0)) (kp.le.trans (lower 1))))
        (lower 3) kp.le (mul_nonneg (mul_nonneg (kp.le.trans (lower 0)) (kp.le.trans (lower 1))) (kp.le.trans (lower 2)))
    exact (show κ^8=κ^4*(κ*κ*κ*κ) by ring).le.trans
      (mul_le_mul (limites_del_producto sp kp.le _ _ hi hj).1 min (by positivity)
        (by unfold pesoContinuo; positivity))
  have seq : ∀ᶠ n : ℕ in atTop,b*κ^8≤A+D/(n:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n np
    have nr : 0<(n:ℝ) := by exact_mod_cast np
    have low : (n:ℝ)^2*κ^8≤sumaDeNumerador n p r c := by
      calc _ = ∑ _ : Cell n,κ^8 := by simp [Fintype.card_prod,nsmul_eq_mul,pow_two]
           _ ≤ _ := Finset.sum_le_sum (fun e _ => one (medio_admisible e.1.isLt) (medio_admisible e.2.isLt))
    have scaled:=mul_le_mul_of_nonneg_left low bp.le
    have s : b*κ^8≤b*sumaDeNumerador n p r c/(n:ℝ)^2 :=
      (le_div_iff₀ (pow_pos nr 2)).mpr (by linarith only [scaled,show b*((n:ℝ)^2*κ^8)=b*κ^8*n^2 by ring])
    have approx:=error_integral_del_cruce sp kp.le lp bp.le n np hr hc
    change |A-_|≤D/(n:ℝ) at approx
    linarith only [s,(abs_le.mp approx).1]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (by
    simpa using (tendsto_const_nhds (x:=A)).add (tendsto_const_div_atTop_nhds_zero_nat D)) seq

theorem integral_del_cociente_del_articulo {P p b κ M L B} (rama : RamaDensa P p b κ M L B) :
    integralTablero (fun r c => gammaDelPerfil (p 0) (b 0) r c/perfilDirectoContinuo (p 0) (b 0) r c)=b 0 := by
  have hz : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have pos:= (rama.euler 0 hz).coef
  have eq {r c} (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
      gammaDelPerfil (p 0) (b 0) r c/perfilDirectoContinuo (p 0) (b 0) r c=
        (b 0*((p 0).fila r:ℝ))*((p 0).columna c:ℝ) := by
    rw [gamma_en_el_cuadrado]
    exact mul_div_cancel_right₀ _ ((mul_pos pos (pow_pos rama.kp 8)).trans_le
      (piso_integral_del_cruce (rama.espacio 0 hz) rama.kp rama.lp pos hr hc)).ne'
  obtain ⟨row,col⟩:=rama.normaliza 0 hz
  unfold integralTablero integralFila
  calc _ = ∫ r in (0:ℝ)..1,(b 0)*((p 0).fila r:ℝ) := by
          apply intervalIntegral.integral_congr; intro r hr
          rw [uIcc_of_le zero_le_one] at hr
          calc _ = ∫ c in (0:ℝ)..1,(b 0*((p 0).fila r:ℝ))*((p 0).columna c:ℝ) := by
                  apply intervalIntegral.integral_congr; intro c hc
                  rw [uIcc_of_le zero_le_one] at hc; exact eq hr hc
               _ = _ := by rw [intervalIntegral.integral_const_mul,col,mul_one]
       _ = b 0 := by rw [intervalIntegral.integral_const_mul,row,mul_one]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_del_cociente_del_articulo
