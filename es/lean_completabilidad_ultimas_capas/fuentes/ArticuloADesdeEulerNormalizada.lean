import R15ParaLaRamaCompleta
import EntradasDelArticuloDesdeLasMasas
import LimitesDeCapasDesdeElPerfilYPrimerOrden
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Limites Perfil
open scoped Topology
/-- Branch data with the physical normalization at zero. The endpoint continuity
    and the choice of finite Simkin neighborhoods are recovered inside the proof. -/
theorem premisas_del_articulo_desde_euler_normalizada {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (g0 : NormalizacionR15 (p 0))
    (locales : admisibleParaConteo (P 0) → ∀ η : ℝ,0<η → ∃ S : (n : ℕ) → Finset (Placement n),
      (∀ n,S n⊆nivel n n) ∧ Real.exp (valorCentrado (P 0)-η)≤liminf (raizDelConteo (fun n=>(S n).card)) atTop) :
    RamaDensa P p b κ M L (1/κ^4) ∧ ContinuidadEnElLleno p b ∧ CotaDePrimerOrden (valorCentrado (P 0)) :=
  entradas_para_las_capas_desde_las_masas kp k1 m1 lp eq sp
    (control_R15_hasta_el_lleno kp k1 m1 lp eq sp g0) locales

theorem ley_de_capas_desde_euler_normalizada {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) (g0 : NormalizacionR15 (p 0))
    (locales : admisibleParaConteo (P 0) → ∀ η : ℝ,0<η → ∃ S : (n : ℕ) → Finset (Placement n),
      (∀ n,S n⊆nivel n n) ∧ Real.exp (valorCentrado (P 0)-η)≤liminf (raizDelConteo (fun n=>(S n).card)) atTop)
    (K : ℕ) :
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n=>fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0))) ∧
    Tendsto (fun n=>conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil b 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ=>∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0)) := by
  obtain ⟨r,cont,prim⟩:=premisas_del_articulo_desde_euler_normalizada kp k1 m1 lp eq sp g0 locales
  exact conclusiones_de_capas_fijas r cont prim K
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.premisas_del_articulo_desde_euler_normalizada
#print axioms ArticuloA.Historias.ley_de_capas_desde_euler_normalizada
