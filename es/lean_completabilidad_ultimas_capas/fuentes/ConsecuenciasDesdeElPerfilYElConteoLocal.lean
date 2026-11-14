import DelConteoLocalDeSimkinAlGlobal
import RamaMedidaConNormalizacionDeducida
import CorolariosDelPerfilDelArticulo
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter Perfil Limites
open scoped Topology

theorem consecuencias_desde_euler_y_simkin {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ} {κ M L : ℝ}
    (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (space : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (cont : ContinuidadEnElLleno p b)
    (S : (n : ℕ)→Finset (Placement n)) (sub : ∀ n,S n⊆nivel n n)
    (localBound : admisibleParaConteo (P 0) → Real.exp (valorCentrado (P 0))≤
      liminf (raizDelConteo (fun n => (S n).card)) atTop)
    (K : ℕ) (inv : ∀ h,0<h → h≤K → concentracionInversaFisica p b h) :
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n => fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0))) ∧
    Tendsto (fun n => conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil b 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ => ∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0)) := by
  have rama:=construir_rama_desde_la_euler_medida kp k1 m1 lp eq space cont
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using eq 0 ⟨le_rfl,by norm_num⟩
  exact consecuencias_del_articulo rama cont (primer_orden_para_el_perfil full S sub localBound) K inv

theorem cota_positiva_desde_euler_y_simkin {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ} {κ M L : ℝ}
    (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (space : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (cont : ContinuidadEnElLleno p b)
    (S : (n : ℕ)→Finset (Placement n)) (sub : ∀ n,S n⊆nivel n n)
    (localBound : admisibleParaConteo (P 0) → Real.exp (valorCentrado (P 0))≤
      liminf (raizDelConteo (fun n => (S n).card)) atTop) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2 :=
  (consecuencias_desde_euler_y_simkin kp k1 m1 lp eq space cont S sub localBound 0
    (fun _ hp hu => by omega)).1
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.consecuencias_desde_euler_y_simkin
#print axioms ArticuloA.Historias.cota_positiva_desde_euler_y_simkin
