import EstabilidadDeLasTransversalesNormalizadas
import ControlDeLaDensidadSeparada
import MasaYEnergiaDeUnaCuerda
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Filter Perfil
theorem error_sobre_el_intervalo (p q : FactoresContinuos) (i : Fin 4) :
    masaExterior (fun j y=>|camposFisicos p j y-camposFisicos q j y|) i=∫ s,errorEntreCamposR15 p q i s ∂marginalRef i := by
  have ref : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
  rw [masaExterior,intervalIntegral.integral_of_le (extremosF i),←ref]
  apply integral_congr_ae
  filter_upwards [linea_en_dominio i] with s hs
  simp only [errorEntreCamposR15,campoR15,recorte_fijo i hs,camposFisicos]

theorem cuatro_masas_y_el_normalizador {P Q p q x y b c κ M L m}
    (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c) (gp : NormalizacionR15 p) (gq : NormalizacionR15 q)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (kp : 0<κ) (k1 : κ≤1) (lp : 0≤L)
    (mp : 0<m) (lo : m≤b) :
    |b-c|≤constanteDeLasVacancias κ*distanciaTableros P Q ∧
      (∑ i,masaExterior (fun j y=>|camposFisicos p j y-camposFisicos q j y|) i)≤
        (4*constanteDeLasVacancias κ/m+2)*distanciaTableros P Q := by
  let Δ:=distanciaTableros P Q
  let H:=constanteDeLasVacancias κ
  have v:=control_fisico_de_V ex ey sp sq kp k1 lp
  refine ⟨(estabilidad_del_normalizador gp gq sp sq lp).trans v,?_⟩
  have rc (i : Fin 4) (h : i.val<2) : (∫ s,errorEntreCamposR15 p q i s ∂marginalRef i)≤(2*H*Δ)/m := by
    have ref : marginalRef i=unidad := by
      rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;>
        exact Measure.restrict_congr_set Ioc_ae_eq_Icc
    rw [ref]
    have a:=estabilidad_de_transversal_R15 gp gq sp sq lp ex.coef i h (c:=c)
    have pos : 0≤∫ s,errorEntreCamposR15 p q i s ∂unidad := integral_nonneg (fun _=>abs_nonneg _)
    apply (le_div_iff₀ mp).mpr
    calc
      _ = m*(∫ s,errorEntreCamposR15 p q i s ∂unidad) := mul_comm .. 
      _ ≤ b*(∫ s,errorEntreCamposR15 p q i s ∂unidad) := mul_le_mul_of_nonneg_right lo pos
      _ ≤ _ := a.trans ((mul_le_mul_of_nonneg_left v (by norm_num : (0:ℝ)≤2)).trans_eq (by dsimp [H,Δ]; ring))
  simp only [Fin.sum_univ_four,error_sobre_el_intervalo]
  have res:=add_le_add (add_le_add (add_le_add (rc 0 (by decide)) (rc 1 (by decide)))
    (masa_del_error_oblicuo ex ey 2 (by decide))) (masa_del_error_oblicuo ex ey 3 (by decide))
  exact res.trans_eq (by dsimp [H,Δ]; ring)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_sobre_el_intervalo
#print axioms ArticuloA.Historias.cuatro_masas_y_el_normalizador
