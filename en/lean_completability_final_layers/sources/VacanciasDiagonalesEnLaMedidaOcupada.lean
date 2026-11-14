import ContraccionDeLasMarginalesFisicas
import CamposMediblesDeLaRama
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
def errorEntreCamposR15 (p q : FactoresContinuos) (i : Fin 4) (s : ℝ) := |campoR15 p i s-campoR15 q i s|

theorem continua_diferencia_de_linea {p q κ M L} (sp : ControlEspacial p κ M L)
    (sq : ControlEspacial q κ M L) (lp : 0≤L) (i : Fin 4) : Continuous (errorEntreCamposR15 p q i) :=
  ((continuo_de_campo sp lp i).sub (continuo_de_campo sq lp i)).abs

theorem error_de_linea_acotado {p q κ M L} (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L)
    (i : Fin 4) (s : ℝ) : ‖errorEntreCamposR15 p q i s‖≤2*M := by
  simp only [errorEntreCamposR15,Real.norm_eq_abs,abs_abs]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (a:=campoR15 p i s) (NNReal.coe_nonneg _),abs_of_nonneg (a:=campoR15 q i s) (NNReal.coe_nonneg _)]
  linarith only [(banda_de_campo sp i s).2,(banda_de_campo sq i s).2]

theorem masa_del_error_oblicuo {P Q p q x y b c}
    (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c) (i : Fin 4) (di : 2 ≤ i.val) :
    (∫ t,errorEntreCamposR15 p q i t ∂marginalRef i)≤distanciaTableros P Q := by
  apply le_trans _ (contraccion_marginal_en_L1 P Q i)
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [masa_de_linea_normalizada ex i,masa_de_linea_normalizada ey i] with t hx hy
  simp only [coefLinea,if_neg (not_lt.mpr di),one_mul] at hx hy
  change |campoR15 p i t-campoR15 q i t|=|(P.m i t:ℝ)-Q.m i t|
  rw [hx,hy,show 1-campoR15 p i t-(1-campoR15 q i t)=-(campoR15 p i t-campoR15 q i t) by ring,abs_neg]

theorem error_oblicuo_ponderado {P Q p q x y b c κ M L} (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (lp : 0≤L) (k1 : κ≤1)
    (i : Fin 4) (di : 2 ≤ i.val) :
    (∫ z,(Q.ν z:ℝ)*errorEntreCamposR15 p q i (coord i z) ∂cuadrado)≤(1-κ)*distanciaTableros P Q := by
  let w:=errorEntreCamposR15 p q i
  have co:=continua_diferencia_de_linea sp sq lp i
  have cap:=error_de_linea_acotado sp sq i
  have it : Integrable w (marginalRef i) := integrable_acotada_probabilidad co.measurable cap
  have iw : Integrable (fun t=>(Q.m i t:ℝ)*w t) (marginalRef i) := by
    simpa only [mul_comm] using (Q.m_integrable i).bdd_mul co.measurable.aestronglyMeasurable ⟨_,cap⟩
  rw [adjuncion Q.ley i _ co.measurable]
  apply le_trans _ (mul_le_mul_of_nonneg_left (masa_del_error_oblicuo ex ey i di) (sub_nonneg.mpr k1))
  rw [←integral_const_mul]
  apply integral_mono_ae iw (it.const_mul (1-κ))
  filter_upwards [masa_de_linea_normalizada ey i] with t eq
  rw [eq]
  exact mul_le_mul_of_nonneg_right (by simpa [coefLinea,not_lt.mpr di] using
    (sub_le_sub_left (banda_de_campo sq i t).1 1)) (abs_nonneg _)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.continua_diferencia_de_linea
#print axioms ArticuloA.Historias.error_de_linea_acotado
#print axioms ArticuloA.Historias.masa_del_error_oblicuo
#print axioms ArticuloA.Historias.error_oblicuo_ponderado
