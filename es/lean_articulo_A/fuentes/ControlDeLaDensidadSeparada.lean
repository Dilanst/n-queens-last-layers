import VacanciasDiagonalesEnLaMedidaOcupada
import DiferenciaDeDensidadesSinDosVacancias
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
def constanteDeLasVacancias (κ : ℝ) := 1/κ^2+2*(1-κ)/κ^3

theorem control_fisico_de_V {P Q p q x y b c κ M L} (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (kp : 0<κ) (k1 : κ≤1) (lp : 0≤L) :
    distanciaEnMedida cuadrado (densidadSeparada p b) (densidadSeparada q c)≤
      constanteDeLasVacancias κ*distanciaTableros P Q := by
  let W:=fun (i : Fin 4) (z : ℝ×ℝ)=>(Q.ν z:ℝ)*errorEntreCamposR15 p q i (coord i z)
  have iw (i : Fin 4) : Integrable (W i) cuadrado := by
    simpa only [W,mul_comm] using Q.masaFinita.bdd_mul
      (((continua_diferencia_de_linea sp sq lp i).measurable.comp (coord_medible i)).aestronglyMeasurable)
      ⟨2*M,fun z=>error_de_linea_acotado sp sq i (coord i z)⟩
  have idn : Integrable (fun z=>|(P.ν z:ℝ)-Q.ν z|) cuadrado := (P.masaFinita.sub Q.masaFinita).abs
  have isep:=((separada_integrable b sp lp).sub (separada_integrable c sq lp)).abs
  have ij:=(idn.const_mul (1/κ^2)).add (((iw 2).add (iw 3)).const_mul (1/κ^3))
  have bd : ∀ᵐ z ∂cuadrado, |densidadSeparada p b z-densidadSeparada q c z|≤
      (1/κ^2)*|(P.ν z:ℝ)-Q.ν z|+(1/κ^3)*(W 2 z+W 3 z) := by
    filter_upwards [densidad_en_factores_recortados ex,densidad_en_factores_recortados ey] with z h g
    exact quitar_dos_vacancias kp (NNReal.coe_nonneg _) (banda_de_campo sp 2 _).1 (banda_de_campo sp 3 _).1
      (banda_de_campo sq 2 _).1 (banda_de_campo sq 3 _).1 h g
  have h:=integral_mono_ae isep ij bd
  simp only [Pi.add_apply,Pi.sub_apply] at h
  have sumI : Integrable (fun z=>W 2 z+W 3 z) cuadrado := (iw 2).add (iw 3)
  rw [integral_add (idn.const_mul _) (sumI.const_mul _),
    integral_const_mul,integral_const_mul,integral_add (iw 2) (iw 3)] at h
  let Δ:=distanciaTableros P Q
  have hd : (∫ z,W 2 z ∂cuadrado)≤(1-κ)*Δ :=
    error_oblicuo_ponderado ex ey sp sq lp k1 2 (by decide)
  have ha : (∫ z,W 3 z ∂cuadrado)≤(1-κ)*Δ :=
    error_oblicuo_ponderado ex ey sp sq lp k1 3 (by decide)
  change distanciaEnMedida cuadrado (densidadSeparada p b) (densidadSeparada q c)≤
    (1/κ^2)*Δ+(1/κ^3)*_ at h
  apply h.trans
  apply (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add hd ha) (by positivity : 0≤1/κ^3)) _).trans_eq
  unfold constanteDeLasVacancias; dsimp only [Δ]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_fisico_de_V
