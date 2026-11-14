import EmpalmeDeLaRamaEnMasaUno
import ControlComunSoloEnElInterior
import ArticuloADesdeEulerNormalizada
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil Limites
open scoped Topology
/-- The common spatial Lipschitz estimate is a consequence.
    Existence of the measured branch and its zeroth-order bands are explicit. -/
theorem articulo_A_desde_el_perfil_interior {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M m lo hi : ℝ} (kp : 0<κ) (k1 : κ≤1) (mp : 0<m) (mm : 1≤M) (lp : 0<lo)
    (eq : ∀ x∈Ioc (0:ℝ) (1/2),EulerFisica (P x) (p x) x.toNNReal (b x))
    (coef : ∀ x∈Ioc (0:ℝ) (1/2),b x∈Icc lo hi)
    (cp : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,ContinuousOn (camposFisicos (p x) i) (rangoF i))
    (band : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,∀ s∈rangoF i,
      if (i:Fin 4).val<2 then m≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤M
      else κ≤camposFisicos (p x) i s ∧ camposFisicos (p x) i s≤1)
    : ∃ (P₀ : TableroMedido) (p₀ : FactoresContinuos) (b₀ : ℝ),
      EulerFisica P₀ p₀ 0 b₀ ∧ NormalizacionR15 p₀ ∧
      (∀ η : ℝ,0<η → ∃ d : ℝ,0<d ∧ ∀ x∈Ioc 0 (1/2:ℝ),x<d →
        |b₀-b x|≤η ∧ (∑ g,masaExterior (fun i s=>|camposFisicos (p x) i s-camposFisicos p₀ i s|) g)≤η) ∧
      ((admisibleParaConteo P₀ → ∀ η : ℝ,0<η → ∃ S : (n : ℕ) → Finset (Placement n),
        (∀ n,S n⊆nivel n n) ∧ Real.exp (valorCentrado P₀-η)≤liminf (raizDelConteo (fun n=>(S n).card)) atTop) →
      ∀ K : ℕ,
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n=>fracReal n h) atTop (𝓝 (fraccionDelPerfil (completarEnCero b b₀) 0))) ∧
    Tendsto (fun n=>conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil (completarEnCero b b₀) 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ=>∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil (completarEnCero b b₀) (((j:ℝ)+1-s)/n))) atTop (𝓝 0))) := by
  obtain ⟨L,Lp,sp⟩:=control_espacial_en_la_rama_abierta kp mp mm lp eq coef cp band
  have low:=lt_min mp kp
  have one:=(min_le_right m κ).trans k1
  obtain ⟨P₀,p₀,b₀,g₀,ec,sc⟩:=extender_rama_desde_el_interior low one mm Lp eq sp
  have g : NormalizacionR15 (completarEnCero p p₀ 0) := by simpa [completarEnCero] using g₀
  refine ⟨P₀,p₀,b₀,by simpa [completarEnCero] using ec 0 ⟨le_rfl,by norm_num⟩,g₀,?_,?_⟩
  · intro η hη
    obtain ⟨d,hd,lim⟩:=control_R15_hasta_el_lleno low one mm Lp ec sc g η hη
    refine ⟨d,hd,?_⟩
    intro x hx xd
    simpa [completarEnCero,ne_of_gt hx.1] using lim x ⟨hx.1.le,hx.2⟩ xd
  · intro localCount K
    apply ley_de_capas_desde_euler_normalizada low one mm Lp ec sc g _ K
    simpa [completarEnCero] using localCount
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.articulo_A_desde_el_perfil_interior
