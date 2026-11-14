import DiferenciaDeDensidadesSinDosVacancias
import ContraccionDeLasMarginalesFisicas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩

def NormalizacionR15 (p : FactoresContinuos) : Prop :=
  ∀ i : Fin 4,i.val<2 → (∫ s,campoR15 p i s ∂unidad)=1

theorem normalizacion_R15_en_masa_interior {P p x b} (e : EulerFisica P p x b) (xp : 0<x) :
    NormalizacionR15 p := by
  intro i rc
  have one:=masa_transversal_reescalada e xp i rc
  rw [intervalIntegral.integral_of_le zero_le_one] at one
  have ref : unidad=volume.restrict (Ioc (0:ℝ) 1) := Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have dom : rangoF i=Icc (0:ℝ) 1 := by
    rcases (show i=0 ∨ i=1 by omega) with rfl|rfl <;> rfl
  rw [ref]
  apply Eq.trans _ one
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (a:=(0:ℝ)) (b:=1))] with s hs
  exact congrArg (fun z=>(factorF p i z:ℝ)) (recorte_fijo i (dom ▸ ⟨hs.1.le,hs.2⟩))

theorem proyeccion_de_V_con_prueba (p : FactoresContinuos) (b : ℝ) (g : NormalizacionR15 p)
    (i : Fin 4) (rc : i.val<2) (w : ℝ→ℝ) :
    (∫ z,densidadSeparada p b z*w (coord i z) ∂cuadrado)=b*∫ t,campoR15 p i t*w t ∂unidad := by
  rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
  · calc
      _ = ∫ z,b*((campoR15 p 0 z.1*w z.1)*campoR15 p 1 z.2) ∂cuadrado := by
        apply integral_congr_ae; filter_upwards with z; dsimp [densidadSeparada,coord]; ring
      _ = _ := by
        rw [integral_const_mul,cuadrado,integral_prod_mul (fun t=>campoR15 p 0 t*w t),g 1 (by decide),mul_one]
  · calc
      _ = ∫ z,b*(campoR15 p 0 z.1*(campoR15 p 1 z.2*w z.2)) ∂cuadrado := by
        apply integral_congr_ae; filter_upwards with z; dsimp [densidadSeparada,coord]; ring
      _ = _ := by
        rw [integral_const_mul,cuadrado,integral_prod_mul _ (fun t=>campoR15 p 1 t*w t),g 0 (by decide),one_mul]

theorem integral_de_V_igual_a_b (p : FactoresContinuos) (b : ℝ) (g : NormalizacionR15 p) :
    (∫ z,densidadSeparada p b z ∂cuadrado)=b := by
  simpa only [mul_one,g 0 (by decide)] using proyeccion_de_V_con_prueba p b g 0 (by decide) (fun _=>1)

theorem estabilidad_del_normalizador {p q κ M L} {b c : ℝ} (gp : NormalizacionR15 p) (gq : NormalizacionR15 q)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (lp : 0≤L) :
    |b-c|≤distanciaEnMedida cuadrado (densidadSeparada p b) (densidadSeparada q c) := by
  have eq:=integral_sub (separada_integrable b sp lp) (separada_integrable c sq lp)
  rw [integral_de_V_igual_a_b p b gp,integral_de_V_igual_a_b q c gq] at eq
  rw [←eq]
  exact norm_integral_le_integral_norm (μ:=cuadrado) (fun z=>densidadSeparada p b z-densidadSeparada q c z)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_R15_en_masa_interior
#print axioms ArticuloA.Historias.proyeccion_de_V_con_prueba
#print axioms ArticuloA.Historias.integral_de_V_igual_a_b
#print axioms ArticuloA.Historias.estabilidad_del_normalizador
