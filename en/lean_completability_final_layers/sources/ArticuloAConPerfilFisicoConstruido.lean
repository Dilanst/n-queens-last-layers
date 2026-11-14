import ArticuloADesdeElProductoMedibleDeDEF
import ExistenciaDelTableroDeDEFEnElInterior
import EntradaDeSimkinConElConteoCompleto
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology
theorem articulo_A_con_perfil_fisico_construido :
    ∃ (P : ℝ→TableroMedido) (a : ℝ→ℝ) (p : ℝ→FactoresContinuos),
      (∀ x∈Ioc (0:ℝ) (1/2),EulerFisica (P x) (p x) x.toNNReal (a x*x^2) ∧
        (∀ i,Continuous (camposFisicos (p x) i)) ∧ ∀ i,∀ s∈rangoF i,0<camposFisicos (p x) i s) ∧
      ∃ (P₀ : TableroMedido) (p₀ : FactoresContinuos) (b₀ : ℝ),
      EulerFisica P₀ p₀ 0 b₀ ∧ NormalizacionR15 p₀ ∧
      (∀ η : ℝ,0<η → ∃ d : ℝ,0<d ∧ ∀ x∈Ioc 0 (1/2:ℝ),x<d →
        |b₀-(a x*x^2)|≤η ∧ (∑ g,masaExterior (fun i s=>|camposFisicos (p x) i s-camposFisicos p₀ i s|) g)≤η) ∧
      ((admisibleParaConteo P₀ → ∀ η : ℝ,0<η → ∃ S : (n : ℕ) → Finset (Placement n),
        (∀ n,S n⊆nivel n n) ∧ Real.exp (valorCentrado P₀-η)≤liminf (raizDelConteo (fun n=>(S n).card)) atTop) →
      ∀ K : ℕ,
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n=>fracReal n h) atTop (𝓝 (fraccionDelPerfil (completarEnCero (fun x=>a x*x^2) b₀) 0))) ∧
    Tendsto (fun n=>conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil (completarEnCero (fun x=>a x*x^2) b₀) 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ=>∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil (completarEnCero (fun x=>a x*x^2) b₀) (((j:ℝ)+1-s)/n))) atTop (𝓝 0))) := by
  obtain ⟨P,a,f,data⟩:=existencia_de_la_rama_medible_de_DEF
  obtain ⟨p,reg,terminal⟩:=articulo_A_desde_el_producto_medible (P:=P) (a:=a) (f:=f) data
  exact ⟨P,a,p,reg,terminal⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.articulo_A_con_perfil_fisico_construido
