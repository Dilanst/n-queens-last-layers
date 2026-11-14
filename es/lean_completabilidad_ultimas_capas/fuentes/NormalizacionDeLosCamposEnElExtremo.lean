import RepresentanteFisicoDeLosCuatroLimites
import IdentidadesDeLaDensidadSeparada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
theorem normalizacion_de_los_campos_en_el_extremo {p : ℕ→FactoresContinuos} {p₀ : FactoresContinuos}
    {κ M L : ℝ} (sp : ∀ j,ControlEspacial (p j) κ M L) (lp : 0≤L) (norm : ∀ j,NormalizacionR15 (p j))
    (lc : ∀ i,∀ s∈rangoF i,Tendsto (fun j=>camposFisicos (p j) i s) atTop (𝓝 (camposFisicos p₀ i s))) :
    NormalizacionR15 p₀ := by
  letI : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
  intro i rc
  have pt s : Tendsto (fun j=>campoR15 (p j) i s) atTop (𝓝 (campoR15 p₀ i s)) := lc i _ (recorte_dentro i s)
  have integrals:=tendsto_integral_of_dominated_convergence (μ:=unidad) (fun _=>M)
    (fun j=>(continuo_de_campo (sp j) lp i).aestronglyMeasurable) (integrable_const M)
    (fun j=>Eventually.of_forall (fun s=>by
      change ‖(factorF (p j) i (recorte i s):ℝ)‖≤M
      simpa using (banda_de_campo (sp j) i s).2)) (Eventually.of_forall pt)
  exact tendsto_nhds_unique integrals (tendsto_const_nhds.congr (fun j=>(norm j i rc).symm))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_de_los_campos_en_el_extremo
