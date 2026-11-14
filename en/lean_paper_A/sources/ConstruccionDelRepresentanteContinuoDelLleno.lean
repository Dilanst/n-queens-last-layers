import ContinuidadAlLlenoDesdeLasMasasL1
import Mathlib.Topology.UniformSpace.UniformApproximation
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Filter Perfil
open scoped Topology Uniformity
/-- Pairwise control along a filter, including the actual one-sided limit of positive densities.
    No endpoint field or modulus of continuity is an input. -/
theorem representante_continuo_desde_cauchy_de_la_rama {ι : Type*} (l : Filter ι) [NeBot l]
    (p : ι→FactoresContinuos) (x : ι→ℝ≥0) (b : ι→ℝ) {K B : ℝ} (hk : 0≤K) (hB : 0≤B)
    (cp : ∀ m g,ContinuousOn (camposFisicos (p m) g) (rangoF g))
    (cap : ∀ m g,∀ s∈rangoF g,|camposFisicos (p m) g s|≤K)
    (bcap : ∀ m,|b m|≤B)
    (eq : ∀ m i,∀ᵐ t ∂marginalRef i,b m*integralFisica (p m) i t=1-holguraLinea (p m) (x m) i t)
    (cauchy : ∀ u : ℝ,0<u → ∀ᶠ mn : ι×ι in l ×ˢ l,
      |(x mn.2:ℝ)-x mn.1|≤u ∧ |b mn.2-b mn.1|≤u ∧
      (∑ g,masaExterior (fun j y=>|camposFisicos (p mn.1) j y-camposFisicos (p mn.2) j y|) g)≤u) :
    ∃ P₀ : Fin 4→ℝ→ℝ,∀ i,ContinuousOn (P₀ i) (rangoF i) ∧
      TendstoUniformlyOn (fun m=>camposFisicos (p m) i) (P₀ i) l (rangoF i) := by
  let H:=K^2*(1+K^3+B*K^2)
  have hn : 0≤H := by dsimp [H]; positivity
  let P₀:=fun i s=>limUnder l (fun m=>camposFisicos (p m) i s)
  refine ⟨P₀,?_⟩
  intro i
  have cu : UniformCauchySeqOn (fun m=>camposFisicos (p m) i) l (rangoF i) := by
    intro v hv
    obtain ⟨ε,ep,vin⟩:=Metric.mem_uniformity_dist.mp hv
    let u:=ε/(H+1)
    have up : 0<u := div_pos ep (by linarith)
    have um : u*(H+1)=ε := div_mul_cancel₀ _ (by linarith)
    filter_upwards [cauchy u up] with mn hmn
    intro s hs
    have e j:=ecuacion_puntual_sin_lipschitz (x j) (cp j) i (eq j i) s hs
    have jd:=control_de_la_cavidad_por_L1 (cp mn.1) (cp mn.2) (cap mn.1) (cap mn.2) i hs
    have sub:=suma_de_tres_acotada_por_las_cuatro i _ (masa_exterior_no_negativa
      (fun j y=>abs_nonneg (camposFisicos (p mn.1) j y-camposFisicos (p mn.2) j y)))
    have dj:=jd.trans (mul_le_mul_of_nonneg_left (sub.trans hmn.2.2) (sq_nonneg K))
    have coeff : |(if i.val<2 then (x mn.2:ℝ) else 1)-(if i.val<2 then (x mn.1:ℝ) else 1)|≤u := by
      split_ifs
      · exact hmn.1
      · simpa using up.le
    have bound:=diferencia_entre_dos_ecuaciones_de_euler hk (cap mn.1 i s hs) (cap mn.2 i s hs)
      (bcap mn.1) (techo_de_cavidad hk (cap mn.2) i hs) (e mn.1) (e mn.2) coeff hmn.2.1 (by rwa [abs_sub_comm])
    apply vin
    rw [Real.dist_eq]
    exact bound.trans_lt (show H*u<ε by linarith only [um,up])
  have unif : TendstoUniformlyOn (fun m=>camposFisicos (p m) i) (P₀ i) l (rangoF i) :=
    cu.tendstoUniformlyOn_of_tendsto (fun s hs=>(cu.cauchy_map hs).le_nhds_lim)
  exact ⟨unif.continuousOn (Eventually.of_forall (fun m=>cp m i)),unif⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.representante_continuo_desde_cauchy_de_la_rama
