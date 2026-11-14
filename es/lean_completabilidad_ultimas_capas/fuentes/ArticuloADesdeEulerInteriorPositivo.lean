import ArticuloADesdeLaRamaEstrictamenteInterior
import BandasPuntualesSinHipotesisUniformes
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology
theorem articulo_A_desde_euler_interior_positivo {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    (eq : ∀ x∈Ioc (0:ℝ) (1/2),EulerFisica (P x) (p x) x.toNNReal (b x))
    (cp : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,ContinuousOn (camposFisicos (p x) i) (rangoF i))
    (pos : ∀ x∈Ioc (0:ℝ) (1/2),∀ i,∀ s∈rangoF i,0<camposFisicos (p x) i s)
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
  have ep : 0<techoDEF35 := exp_pos _
  have kp : 0<sueloDiagonalDEF35 := by unfold sueloDiagonalDEF35; positivity
  have k1 : sueloDiagonalDEF35≤1 := by
    unfold sueloDiagonalDEF35
    exact (div_le_one (by positivity)).mpr (by nlinarith only [mul_nonneg (sq_nonneg techoDEF35) (sq_nonneg techoDEF35)])
  have bands x (hx : x∈Ioc (0:ℝ) (1/2)) :=
    bandas_de_orden_cero_sobre_la_rama (eq x hx) (Real.toNNReal_pos.mpr hx.1)
      (by simpa only [Real.coe_toNNReal _ hx.1.le] using hx.2) (cp x hx) (pos x hx)
  exact articulo_A_desde_el_perfil_interior kp k1 (one_div_pos.mpr (pow_pos ep 2)) techoDEF35_al_menos_uno
    (by norm_num : (0:ℝ)<1/2) eq (fun x hx=>(bands x hx).1) cp (fun x hx=>(bands x hx).2)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.articulo_A_desde_euler_interior_positivo
