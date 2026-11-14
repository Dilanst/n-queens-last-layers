import EulerPuntualEnLasCuatroFamilias
import LimiteDelArticuloDesdeLaInversaFisica
import CocienteDeConteos
import LimiteDeCapasFijas
open Set Filter
open scoped Topology
namespace ArticuloA.Historias
open Perfil Limites
noncomputable section

/-- The physical F(x) of the manuscript, at a nonnegative density. -/
def fraccionDelPerfil (b : ℝ→ℝ) (x : ℝ) := (1-x)/b x

private theorem extremo_en_la_malla {p b} (cont : ContinuidadEnElLleno p b) (bp : 0<b 0)
    (t : ℝ) (tp : 0≤t) : Tendsto (fun n : ℕ => fraccionDelPerfil b (t/n)) atTop (𝓝 (1/b 0)) := by
  have x:=tendsto_const_div_atTop_nhds_zero_nat t
  have tail : Tendsto (fun n : ℕ => b (t/n)) atTop (𝓝 (b 0)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    obtain ⟨d,dp,good⟩:=cont (ε/2) (half_pos ep)
    have h1:=(tendsto_order.mp x).2 d dp
    have h2:=(tendsto_order.mp x).2 (1/2:ℝ) (by norm_num)
    filter_upwards [h1,h2] with n less half
    have non : 0≤t/(n:ℝ) := div_nonneg tp (Nat.cast_nonneg _)
    exact (Real.dist_eq ..) ▸ ((good _ ⟨non,half.le⟩ less).1.trans_lt (half_lt_self ep))
  simpa only [fraccionDelPerfil,sub_zero] using
    ((tendsto_const_nhds (x:=(1:ℝ))).sub x).div tail bp.ne'

def concentracionInversaFisica (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (h : ℕ) : Prop :=
  ∀ ε>0,Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (fun z => 1/aDelLleno p b z))
    (integralTablero (fun r c => gammaDelPerfil (p 0) (b 0) r c/perfilDirectoContinuo (p 0) (b 0) r c)) ε)
      atTop (𝓝 0)

/-- Sections 7, 9 and both fixed-K sampling conventions of Section 10.
The inverse input is requested only through the fixed terminal level K. -/
theorem consecuencias_del_articulo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0)))
    (K : ℕ) (inv : ∀ h,0<h → h≤K → concentracionInversaFisica p b h) :
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n => fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0))) ∧
    Tendsto (fun n => conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil b 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ => ∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0)) := by
  have pt:=euler_puntual_de_la_rama rama
  have b0:=(rama.euler 0 (by constructor <;> norm_num)).coef
  have val : fraccionDelPerfil b 0=1/b 0 := by simp [fraccionDelPerfil]
  have pos : 0<fraccionDelPerfil b 0 := val ▸ one_div_pos.mpr b0
  have layer (h : ℕ) (hp : 0<h) (hk : h≤K) :
      Tendsto (fun n => fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0)) := by
    rw [val]; exact limite_con_la_unica_entrada_inversa rama pt cont first h hp (inv h hp hk)
  refine ⟨completabilidad_desde_primer_orden rama pt first,layer,
    limite_conteo K _ pos (soluciones_eventuales_del_primer_orden first) (fun j hj jk => layer j hj jk),?_⟩
  intro s hs
  have each (j : ℕ) (hj : j∈Finset.range K) : Tendsto (fun n : ℕ =>
      Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0) := by
    have num:=layer (j+1) (by omega) (Finset.mem_range.mp hj)
    rw [val] at num
    have den:=extremo_en_la_malla cont b0 ((j:ℝ)+1-s) (by linarith [hs.2,Nat.cast_nonneg (α:=ℝ) j])
    have one : Tendsto (fun n : ℕ => fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n)) atTop (𝓝 1) := by
      simpa only [Pi.div_apply,div_self (one_div_pos.mpr b0).ne'] using num.div den (one_div_pos.mpr b0).ne'
    simpa only [Function.comp_def,Real.log_one] using (Real.continuousAt_log one_ne_zero).tendsto.comp one
  simpa using tendsto_finset_sum (Finset.range K) each

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.consecuencias_del_articulo
