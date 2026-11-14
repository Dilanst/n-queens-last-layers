import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
noncomputable local instance : IsProbabilityMeasure unidad := ⟨by simp [unidad,Real.volume_Icc]⟩
noncomputable local instance : IsProbabilityMeasure cuadrado := by unfold cuadrado; infer_instance

def campoR15 (p : FactoresContinuos) (i : Fin 4) (s : ℝ) : ℝ := factorF p i (recorte i s)
def logR15 (p : FactoresContinuos) (i : Fin 4) (s : ℝ) := Real.log (campoR15 p i s)
def coefLinea (x : ℝ≥0) (i : Fin 4) : ℝ := if i.val<2 then (x:ℝ) else 1

theorem banda_de_campo {p κ M L} (sp : ControlEspacial p κ M L) (i : Fin 4) (s : ℝ) :
    κ≤campoR15 p i s ∧ campoR15 p i s≤M := by
  have ht:=recorte_dentro i s
  refine ⟨(regular_familia sp i).minimo _ ht,?_⟩
  fin_cases i; exacts [sp.Rmax _ ht,sp.Cmax _ ht,sp.Dmax _ ht,sp.Amax _ ht]

theorem continuo_de_campo {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L) (i : Fin 4) :
    Continuous (campoR15 p i) := (continua_de_cota lp (regular_familia sp i).oscilacion).comp_continuous
      (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)

theorem continuo_del_logaritmo {p κ M L} (sp : ControlEspacial p κ M L) (kp : 0<κ) (lp : 0≤L) (i : Fin 4) :
    Continuous (logR15 p i) := (continuo_de_campo sp lp i).log (fun s=>(kp.trans_le (banda_de_campo sp i s).1).ne')

theorem banda_del_logaritmo {p κ M L} (sp : ControlEspacial p κ M L) (kp : 0<κ) (i : Fin 4) (s : ℝ) :
    |logR15 p i s|≤|Real.log κ|+|Real.log M| := by
  obtain ⟨lower,upper⟩:=banda_de_campo sp i s
  have lo:=Real.log_le_log kp lower
  have hi:=Real.log_le_log (kp.trans_le lower) upper
  unfold logR15
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log κ),abs_nonneg (Real.log M)],
    by linarith [le_abs_self (Real.log M),abs_nonneg (Real.log κ)]⟩

theorem masa_de_linea_normalizada {P p x b} (e : EulerFisica P p x b) (i : Fin 4) :
    ∀ᵐ t ∂marginalRef i,(P.m i t:ℝ)=1-coefLinea x i*campoR15 p i t := by
  filter_upwards [linea_en_dominio i,e.linea i] with t ht eq
  unfold campoR15; rw [recorte_fijo i ht]
  change 1-(P.m i t:ℝ)=coefLinea x i*(factorF p i t:ℝ) at eq
  linarith

theorem densidad_en_factores_recortados {P p x b} (e : EulerFisica P p x b) :
    ∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=b*campoR15 p 0 z.1*campoR15 p 1 z.2*
      campoR15 p 2 (coord 2 z)*campoR15 p 3 (coord 3 z) := by
  filter_upwards [e.real,tablero_en_dominio] with z eq hz
  have fixed (i : Fin 4) : campoR15 p i (coord i z)=(factorF p i (coord i z):ℝ) := by
    simp [campoR15,recorte_fijo i (coordenadas_en_dominio hz i)]
  change _=b*campoR15 p 0 (coord 0 z)*campoR15 p 1 (coord 1 z)*_ *_
  simp only [fixed]
  rw [eq]
  dsimp [factorF,pesoContinuo,coord]; ring

theorem log_de_la_densidad_normalizada {P p x b κ M L} (e : EulerFisica P p x b)
    (sp : ControlEspacial p κ M L) (kp : 0<κ) :
    ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=Real.log b+∑ i : Fin 4,logR15 p i (coord i z) := by
  filter_upwards [densidad_en_factores_recortados e] with z hz
  exact log_del_producto e.coef (fun i=>kp.trans_le (banda_de_campo sp i (coord i z)).1) hz

theorem integrable_acotada_probabilidad {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X→ℝ} (mf : Measurable f) {C : ℝ} (h : ∀ z,|f z|≤C) : Integrable f μ :=
  (integrable_const C).mono' mf.aestronglyMeasurable (Eventually.of_forall h)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.banda_de_campo
#print axioms ArticuloA.Historias.continuo_de_campo
#print axioms ArticuloA.Historias.continuo_del_logaritmo
#print axioms ArticuloA.Historias.banda_del_logaritmo
#print axioms ArticuloA.Historias.masa_de_linea_normalizada
#print axioms ArticuloA.Historias.densidad_en_factores_recortados
#print axioms ArticuloA.Historias.log_de_la_densidad_normalizada
#print axioms ArticuloA.Historias.integrable_acotada_probabilidad
