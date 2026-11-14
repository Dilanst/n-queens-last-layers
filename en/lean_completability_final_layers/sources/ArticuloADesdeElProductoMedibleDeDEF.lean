import ArticuloADesdeEulerInteriorPositivo
import EulerFisicaDesdeVacanciasMedibles
import EcuacionesDeFibraDelOptimoMedible
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology
/-- The only Euler equations used here are the density and slack equalities almost everywhere. -/
theorem articulo_A_desde_el_producto_medible {P : ℝ→TableroMedido} {a : ℝ→ℝ} {f : ℝ→Fin 4→ℝ→ℝ}
    (datos : ∀ x∈Ioc (0:ℝ) (1/2),0<a x ∧ (P x).rho=1-x ∧
      (∀ i,Integrable (f x i)) ∧ (∀ i,Measurable (f x i)) ∧ (∀ i y,0≤f x i y) ∧ (∀ i y,|f x i y|≤1) ∧
      (∀ᵐ z ∂cuadrado,((P x).ν z:ℝ)=a x*f x 0 (coord 0 z)*f x 1 (coord 1 z)*f x 2 (coord 2 z)*f x 3 (coord 3 z)) ∧
      ∀ i,∀ᵐ s ∂marginalRef i,(P x).u i s=f x i s)
    : ∃ p : ℝ→FactoresContinuos,
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
  classical
  have one x (hx : x∈Ioc (0:ℝ) (1/2)) : ∃ p : FactoresContinuos,EulerFisica (P x) p x.toNNReal (a x*x^2) ∧
      (∀ i,Continuous (camposFisicos p i)) ∧ ∀ i,∀ s∈rangoF i,0<camposFisicos p i s := by
    obtain ⟨ap,mass,fi,fm,nn,cap,area,line⟩:=datos x hx
    have coef : (x.toNNReal:ℝ)=x := Real.coe_toNNReal _ hx.1.le
    have result:=euler_fisica_desde_vacancias_medibles (x:=x.toNNReal) (by rw [coef]; exact hx.1) ap
      (by rw [coef]; exact mass) fi fm nn cap area line (ecuacion_de_fibra_del_optimo_medible fi fm nn cap area line)
    rwa [coef] at result
  let p (x : ℝ) := if h : x∈Ioc (0:ℝ) (1/2) then (one x h).choose else factoresEnElExtremo (fun _ _=>1)
  have hp x (hx : x∈Ioc (0:ℝ) (1/2)) : EulerFisica (P x) (p x) x.toNNReal (a x*x^2) ∧
      (∀ i,Continuous (camposFisicos (p x) i)) ∧ ∀ i,∀ s∈rangoF i,0<camposFisicos (p x) i s := by
    simpa only [p,dif_pos hx] using (one x hx).choose_spec
  refine ⟨p,hp,?_⟩
  exact articulo_A_desde_euler_interior_positivo (fun x hx=>(hp x hx).1)
    (fun x hx i=>((hp x hx).2.1 i).continuousOn) (fun x hx=>(hp x hx).2.2)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.articulo_A_desde_el_producto_medible
