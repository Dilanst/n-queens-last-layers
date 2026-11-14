import EulerPuntualEnLasCuatroFamilias
import CorolariosDelPerfilDelArticulo
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

open Perfil Set MeasureTheory
open scoped Interval
theorem techo_desde_la_masa {P p x b κ M L} (e : EulerFisica P p x b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) : b≤1/κ^4 := by
  letI : IsFiniteMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
  letI : IsFiniteMeasure cuadrado := by unfold cuadrado; infer_instance
  have ub : ∀ᵐ z ∂cuadrado,b*κ^4≤(P.ν z:ℝ) := by
    filter_upwards [tablero_en_dominio,e.real] with z h eq
    rw [eq]; exact mul_le_mul_of_nonneg_left (limites_del_producto sp kp.le _ _ h.1 h.2).1 e.coef.le
  have mass := integral_mono_ae (integrable_const (μ:=cuadrado) (b*κ^4)) P.masaFinita ub
  have unit : cuadrado.real Set.univ=1 := by
    unfold Measure.real cuadrado
    rw [←univ_prod_univ,Measure.prod_prod]; simp [unidad,Real.volume_Icc]
  rw [integral_const,unit,one_smul] at mass
  change b*κ^4≤P.rho at mass
  rw [e.masa] at mass
  exact (le_div_iff₀ (pow_pos kp 4)).mpr (mass.trans (sub_le_self 1 x.property))

theorem vacancia_en_los_extremos {P p x b κ M L} (e : EulerFisica P p x b) (sp : ControlEspacial p κ M L)
    (lp : 0≤L) : p.diagonal (-1)=1 ∧ p.anti 0=1 := by
  have f:=euler_oblicua_puntual e sp lp false
  have a:=euler_oblicua_puntual e sp lp true
  have fd:=f (-1) (by norm_num [indiceDeLaSeccion,rangoF,extremoIzq,extremoDer])
  have fa:=a 0 (by norm_num [indiceDeLaSeccion,rangoF,extremoIzq,extremoDer])
  norm_num [indiceDeLaSeccion,integralFisica,integralDesplazada,holguraLinea,factorF] at fd fa
  simp only [if_neg (by decide : ¬(3:Fin 4).val<2)] at fa
  constructor <;> apply NNReal.coe_injective <;> push_cast <;> linarith

theorem masa_transversal_reescalada {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (i : Fin 4) (rc : i.val<2) : (∫ t in (0:ℝ)..1,(factorF p i t:ℝ))=1 := by
  have casesRC : i=0 ∨ i=1 := by omega
  have ref : marginalRef i=volume.restrict (Ioc (0:ℝ) 1) := by rcases casesRC with rfl|rfl <;> rfl
  have unit : (∫ _ : ℝ,(1:ℝ) ∂marginalRef i)=1 := by simp [ref,Real.volume_Ioc]
  have eq : ∀ᵐ t ∂marginalRef i,(x:ℝ)*(factorF p i t:ℝ)=P.u i t :=
    (e.linea i).mono (fun _ he => by simpa [holguraLinea,rc] using he.symm)
  have integ:=integral_congr_ae eq
  simp only [integral_const_mul,TableroMedido.u] at integ
  rw [integral_sub (integrable_const _) (P.m_integrable i),unit,masa_de_cada_linea P.ley i] at integ
  change (x:ℝ)*(∫ t,(factorF p i t:ℝ) ∂marginalRef i)=1-P.rho at integ
  rw [e.masa,ref] at integ
  rw [intervalIntegral.integral_of_le zero_le_one]
  have xr : (0:ℝ)<x := xp
  nlinarith

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.techo_desde_la_masa
#print axioms ArticuloA.Historias.vacancia_en_los_extremos
#print axioms ArticuloA.Historias.masa_transversal_reescalada
