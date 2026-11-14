import TangenteSinSupuestoDePositividadDelRival
import OscilacionEspacialDelPeso
open Set MeasureTheory Filter
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

def extremoIzq : Fin 4→ℝ | 0 => 0 | 1 => 0 | 2 => -1 | 3 => 0
def extremoDer : Fin 4→ℝ | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 2
def factorF (p : FactoresContinuos) : Fin 4→ℝ→ℝ≥0 | 0 => p.fila | 1 => p.columna | 2 => p.diagonal | 3 => p.anti
def rangoF (i : Fin 4) := Icc (extremoIzq i) (extremoDer i)
def recorte (i : Fin 4) (s : ℝ) := min (extremoDer i) (max (extremoIzq i) s)
def correccionRC (y : ℝ≥0) (i : Fin 4) := if i.val<2 then Real.log y else 0
def campoPerfil (p : FactoresContinuos) (y : ℝ≥0) (i : Fin 4) (t : ℝ) :=
  correccionRC y i+Real.log (factorF p i (recorte i t))

theorem extremosF (i : Fin 4) : extremoIzq i≤extremoDer i := by fin_cases i <;> norm_num [extremoIzq,extremoDer]
theorem recorte_dentro (i : Fin 4) (s : ℝ) : recorte i s∈rangoF i :=
  ⟨le_min (extremosF i) (le_max_left _ _),min_le_left _ _⟩
theorem recorte_fijo (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) : recorte i s=s := by
  rw [recorte,max_eq_right hs.1,min_eq_right hs.2]
theorem regular_familia {p κ M L} (data : ControlEspacial p κ M L) (i : Fin 4) :
    RegularEn (rangoF i) (factorF p i) κ L := by
  fin_cases i; exacts [data.R,data.C,data.D,data.A]
theorem campo_base_continuo {p κ M L} (data : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) (i : Fin 4) :
    ContinuousOn (fun s => Real.log (factorF p i s)) (rangoF i) :=
  continua_de_cota (div_nonneg lp kp.le) ((regular_familia data i).logarithmos kp)

theorem campo_perfil_integrable (P : TableroMedido) {p κ M L} (data : ControlEspacial p κ M L)
    (kp : 0<κ) (lp : 0≤L) (y : ℝ≥0) : CampoIntegrable P (campoPerfil p y) := by
  have co (i : Fin 4) : Continuous (campoPerfil p y i) := continuous_const.add
    ((campo_base_continuo data kp lp i).comp_continuous (continuous_const.min (continuous_const.max continuous_id))
      (recorte_dentro i))
  have bound (i : Fin 4) : ∃ C,∀ t,‖campoPerfil p y i t‖≤C := by
    obtain ⟨z,_,top⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (extremosF i))
      ((continuousOn_const.add (campo_base_continuo data kp lp i)).norm :
        ContinuousOn (fun x => ‖correccionRC y i+Real.log (factorF p i x)‖) (rangoF i))
    exact ⟨_,fun t => top (recorte_dentro i t)⟩
  refine ⟨fun i => (co i).measurable,?_,?_,?_⟩
  · intro i; obtain ⟨C,bc⟩:=bound i
    simpa only [mul_comm] using P.masaFinita.bdd_mul ((co i).measurable.comp (coord_medible i)).aestronglyMeasurable
      ⟨C,fun z => bc (coord i z)⟩
  · intro i; simpa only [mul_comm] using (P.m_integrable i).bdd_mul (co i).aestronglyMeasurable (bound i)
  · intro i; simpa only [mul_comm] using (P.u_integrable i).bdd_mul (co i).aestronglyMeasurable (bound i)

theorem integral_del_campo {p κ M L} (data : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) (y : ℝ≥0) :
    (∑ i : Fin 4,∫ t,campoPerfil p y i t ∂marginalRef i)=entropiaDeFactores p y := by
  have each (i : Fin 4) : (∫ t,campoPerfil p y i t ∂marginalRef i)=
      (extremoDer i-extremoIzq i)*correccionRC y i+intervaloLog (extremoIzq i) (extremoDer i) (factorF p i) := by
    have ref : marginalRef i=volume.restrict (Ioc (extremoIzq i) (extremoDer i)) := by fin_cases i <;> rfl
    rw [ref,←intervalIntegral.integral_of_le (extremosF i)]
    have eq : EqOn (campoPerfil p y i) (fun x => correccionRC y i+Real.log (factorF p i x))
        (uIcc (extremoIzq i) (extremoDer i)) := by
      rw [uIcc_of_le (extremosF i)]; intro t ht; simp [campoPerfil,recorte_fijo i ht]
    rw [intervalIntegral.integral_congr eq,intervalIntegral.integral_add intervalIntegrable_const
      ((campo_base_continuo data kp lp i).intervalIntegrable_of_Icc (extremosF i)),intervalIntegral.integral_const]
    rfl
  simp_rw [each]
  rw [Fin.sum_univ_four]
  norm_num [show ¬(3:Fin 4).val<2 by decide,extremoDer,extremoIzq,correccionRC,factorF,entropiaDeFactores]
  ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.campo_perfil_integrable
#print axioms ArticuloA.Historias.integral_del_campo
