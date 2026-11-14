import ExtensionDeEulerDeLaFila
import CamposMediblesDeLaRama
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Interval
/-- Only continuity on the four intervals is used here. The two diagonal bounds
    and the normalization of the column are those of the original profile. -/
structure DatosTraslacionFisica (p : FactoresContinuos) (x b κ M : ℝ) : Prop where
  continuos : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)
  diagonal : ∀ i : Fin 4,2 ≤ i.val → ∀ s∈rangoF i,κ≤camposFisicos p i s ∧ camposFisicos p i s≤1
  columna : ∀ t∈unidadCerrada,(p.columna t:ℝ)≤M
  masaCol : (∫ t in (0:ℝ)..1,(p.columna t:ℝ))=1
  euler : ∀ i,∀ s∈rangoF i,b*integralFisica p i s+(if i.val<2 then x else 1)*camposFisicos p i s=1

theorem campo_continuo_por_recorte {p : FactoresContinuos}
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (i : Fin 4) : Continuous (campoR15 p i) :=
  (cp i).comp_continuous (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)

theorem campo_dentro_de_su_intervalo (p : FactoresContinuos) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    campoR15 p i s=camposFisicos p i s := by simp [campoR15,camposFisicos,recorte_fijo i hs]

theorem extremos_diagonales_del_sistema {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (i : Fin 4) (di : 2 ≤ i.val) :
    camposFisicos p i (extremoIzq i)=1 ∧ camposFisicos p i (extremoDer i)=1 := by
  have e1:=h.euler i _ ⟨le_rfl,extremosF i⟩
  have e2:=h.euler i _ ⟨extremosF i,le_rfl⟩
  rcases (show i=2 ∨ i=3 by omega) with rfl|rfl <;>
    norm_num [extremoIzq,extremoDer,integralFisica,integralDesplazada,show ¬(3:Fin 4).val<2 by decide] at e1 e2 ⊢ <;>
    exact ⟨e1,e2⟩

theorem campo_diagonal_fuera_de_su_intervalo {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (i : Fin 4) (di : 2 ≤ i.val) {s : ℝ} (hs : s∉rangoF i) : campoR15 p i s=1 := by
  obtain ⟨iz,de⟩:=extremos_diagonales_del_sistema h i di
  change camposFisicos p i (min (extremoDer i) (max (extremoIzq i) s))=1
  by_cases lo : s≤extremoIzq i
  · rwa [max_eq_left lo,min_eq_right (extremosF i)]
  · have hi : extremoDer i≤s := le_of_lt (lt_of_not_ge (fun hh=>hs ⟨le_of_not_ge lo,hh⟩))
    rwa [max_eq_right ((extremosF i).trans hi),min_eq_left hi]

theorem nucleo_y_fila_del_perfil {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) :
    let R:=filaPorEuler (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) x b
    Continuous R ∧ ∀ s,1/(x+b)≤R s ∧ R s≤1/(x+b*κ^2) ∧
      R s*(x+b*nucleoFilaExtendida (campoR15 p 1) (campoR15 p 2) (campoR15 p 3) s)=1 := by
  have masa : (∫ t in (0:ℝ)..1,campoR15 p 1 t)=1 := by
    apply Eq.trans _ h.masaCol
    apply intervalIntegral.integral_congr; intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact campo_dentro_de_su_intervalo p 1 ht
  have bd:=banda_del_nucleo_de_fila kp.le (campo_continuo_por_recorte h.continuos 1)
    (campo_continuo_por_recorte h.continuos 2) (campo_continuo_por_recorte h.continuos 3)
    (fun t _=>NNReal.coe_nonneg _) masa (fun t=>h.diagonal 2 (by decide) _ (recorte_dentro 2 t))
    (fun t=>h.diagonal 3 (by decide) _ (recorte_dentro 3 t))
  exact fila_extendida_resuelve_euler xn bp kp bd (campo_continuo_por_recorte h.continuos 1)
    (campo_continuo_por_recorte h.continuos 2) (campo_continuo_por_recorte h.continuos 3)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.campo_continuo_por_recorte
#print axioms ArticuloA.Historias.campo_dentro_de_su_intervalo
#print axioms ArticuloA.Historias.extremos_diagonales_del_sistema
#print axioms ArticuloA.Historias.campo_diagonal_fuera_de_su_intervalo
#print axioms ArticuloA.Historias.nucleo_y_fila_del_perfil
