import EulerDeTraslacionDesdeLasMarginales
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
def factoresEnElExtremo (f : Fin 4→ℝ→ℝ) : FactoresContinuos :=
  let u i s := (f i (recorte i s)).toNNReal
  ⟨u 0,u 1,u 2,u 3⟩

theorem representante_en_la_recta (f : Fin 4→ℝ→ℝ) (i : Fin 4) (s : ℝ) :
    camposFisicos (factoresEnElExtremo f) i s=((f i (recorte i s)).toNNReal:ℝ) := by fin_cases i <;> rfl

theorem representante_en_su_intervalo {f : Fin 4→ℝ→ℝ} (pos : ∀ i,∀ s∈rangoF i,0≤f i s) (i : Fin 4) {s : ℝ}
    (hs : s∈rangoF i) : camposFisicos (factoresEnElExtremo f) i s=f i s := by
  rw [representante_en_la_recta,recorte_fijo i hs,Real.coe_toNNReal _ (pos i s hs)]

theorem representante_continuo_sobre_la_recta {f : Fin 4→ℝ→ℝ}
    (cf : ∀ i,ContinuousOn (f i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0≤f i s) (i : Fin 4) :
    Continuous (camposFisicos (factoresEnElExtremo f) i) := by
  have eq : camposFisicos (factoresEnElExtremo f) i=fun s=>f i (recorte i s) := by
    funext s; rw [representante_en_la_recta,Real.coe_toNNReal _ (pos i _ (recorte_dentro i s))]
  rw [eq]; exact (cf i).comp_continuous (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)

theorem control_del_representante_limite {p : ℕ→FactoresContinuos} {f : Fin 4→ℝ→ℝ} {κ M L : ℝ}
    (sp : ∀ j,ControlEspacial (p j) κ M L) (kp : 0≤κ)
    (lim : ∀ i,∀ s∈rangoF i,Tendsto (fun j=>camposFisicos (p j) i s) atTop (𝓝 (f i s))) :
    ControlEspacial (factoresEnElExtremo f) κ M L ∧ (∀ i,∀ s∈rangoF i,0≤f i s) := by
  have band i s (hs : s∈rangoF i) : κ≤f i s ∧ f i s≤M := by
    have per j :=banda_de_campo (sp j) i s
    simp only [campo_dentro_de_su_intervalo _ i hs] at per
    exact ⟨ge_of_tendsto (lim i s hs) (Eventually.of_forall (fun j=>(per j).1)),
      le_of_tendsto (lim i s hs) (Eventually.of_forall (fun j=>(per j).2))⟩
  have pos i s (hs : s∈rangoF i) := kp.trans (band i s hs).1
  have reg (i : Fin 4) : RegularEn (rangoF i) (factorF (factoresEnElExtremo f) i) κ L := by
    refine ⟨fun s hs=>?_,fun u hu v hv=>?_⟩
    · change κ≤camposFisicos _ i s; rw [representante_en_su_intervalo pos i hs]; exact (band i s hs).1
    · change |camposFisicos _ i u-camposFisicos _ i v|≤_
      rw [representante_en_su_intervalo pos i hu,representante_en_su_intervalo pos i hv]
      exact le_of_tendsto ((lim i u hu).sub (lim i v hv)).abs
        (Eventually.of_forall (fun j=>(regular_familia (sp j) i).oscilacion u hu v hv))
  have top i s (hs : s∈rangoF i) : camposFisicos (factoresEnElExtremo f) i s≤M :=
    (representante_en_su_intervalo pos i hs).le.trans (band i s hs).2
  exact ⟨⟨reg 0,reg 1,reg 2,reg 3,top 0,top 1,top 2,top 3⟩,pos⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.representante_en_la_recta
#print axioms ArticuloA.Historias.representante_en_su_intervalo
#print axioms ArticuloA.Historias.representante_continuo_sobre_la_recta
#print axioms ArticuloA.Historias.control_del_representante_limite
