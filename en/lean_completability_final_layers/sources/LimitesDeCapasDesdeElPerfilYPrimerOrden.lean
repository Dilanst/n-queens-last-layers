import ConcentracionInversaDeLaRamaCanonica
import ElBlancoInversoParaLaUltimaCapa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Filter Set Limites
open scoped Topology
theorem inversa_con_el_peso_del_articulo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (primero : CotaDePrimerOrden (valorCentrado (P 0)))
    (h : ℕ) (hh : 0<h) : concentracionInversaFisica p b h := by
  let w:=fun (n : ℕ) (z : Cell n) => 1/aDelLleno p b z
  let j:=h-1
  let target:=fun n : ℕ => blancoInverso j (p ((j:ℝ)/n)) (w n) 1/(n:ℝ)^2
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bp:=(rama.euler 0 zero).coef
  let W:=1/(b 0*κ^8)
  have floor : 0<b 0*κ^8 := mul_pos bp (pow_pos rama.kp _)
  have cap (n) (z : Cell n) : |w n z|≤W := by
    have a:=piso_integral_del_cruce (rama.espacio 0 zero) rama.kp rama.lp bp (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
    change b 0*κ^8≤aDelLleno p b z at a
    change |1/aDelLleno p b z|≤W
    rw [abs_of_nonneg (div_nonneg zero_le_one (floor.le.trans a))]
    exact div_le_div_of_nonneg_left zero_le_one floor a
  have center : Tendsto target atTop (𝓝 (b 0)) := centro_discreto_inverso_tiende_a_b rama cont j
  intro ε ep
  rw [integral_del_cociente_del_articulo rama]
  have tail:=inversa_de_la_rama_en_su_malla rama primero h hh w W (div_nonneg zero_le_one floor.le) cap
    (ε/2) (half_pos ep)
  apply squeeze_zero' _ _ tail
  · apply Eventually.of_forall; intro n; unfold desviacion
    apply Finset.sum_nonneg; intro _ _; split <;> positivity
  · filter_upwards [Metric.tendsto_nhds.mp center (ε/2) (half_pos ep)] with n close
    unfold desviacion
    apply Finset.sum_le_sum; intro Q _
    change (if ε < |Iobs n h (w n) Q-b 0| then _ else 0)≤
      (if ε/2 < |Iobs n h (w n) Q-target n| then _ else 0)
    by_cases high : ε < |Iobs n h (w n) Q-b 0|
    · have tri:=abs_sub_le (Iobs n h (w n) Q) (target n) (b 0)
      rw [Real.dist_eq] at close
      rw [if_pos high,if_pos (by linarith only [tri,close,high])]
    · rw [if_neg high]; split <;> positivity

theorem conclusiones_de_capas_fijas {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (primero : CotaDePrimerOrden (valorCentrado (P 0))) (K : ℕ) :
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) ∧
    (∀ h,0<h → h≤K → Tendsto (fun n => fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0))) ∧
    Tendsto (fun n => conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil b 0)^K)) ∧
    (∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ => ∑ j∈Finset.range K,
      Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0)) :=
  consecuencias_del_articulo rama cont primero K (fun h hh _ => inversa_con_el_peso_del_articulo rama cont primero h hh)
/-- Explicit inputs for the fixed-hole law on the physical queens boards. -/
theorem ley_de_las_capas_desde_euler_y_simkin {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (space : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) (cont : ContinuidadEnElLleno p b)
    (S : (n : ℕ)→Finset (Placement n)) (sub : ∀ n,S n⊆nivel n n)
    (simkin : admisibleParaConteo (P 0) → Real.exp (valorCentrado (P 0))≤
      liminf (raizDelConteo (fun n => (S n).card)) atTop)
    (h : ℕ) (hh : 0<h) :
    Tendsto (fun n => fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0)) := by
  have rama:=construir_rama_desde_la_euler_medida kp k1 m1 lp eq space cont
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using eq 0 ⟨le_rfl,by norm_num⟩
  have first:=primer_orden_para_el_perfil full S sub simkin
  exact (conclusiones_de_capas_fijas rama cont first h).2.1 h hh le_rfl

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.inversa_con_el_peso_del_articulo
#print axioms ArticuloA.Historias.conclusiones_de_capas_fijas
#print axioms ArticuloA.Historias.ley_de_las_capas_desde_euler_y_simkin
