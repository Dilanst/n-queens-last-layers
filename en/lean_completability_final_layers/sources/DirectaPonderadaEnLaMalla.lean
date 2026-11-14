import CotaPositivaDeLasUltimasCapas
open Filter Set
open scoped NNReal Topology
namespace ArticuloA.Historias
open Perfil Limites
noncomputable section


theorem directa_ponderada_desde_cruces (h : ℕ) (hh : 0<h) (a : (n : ℕ)→Cell n→ℝ) (m : ℝ) (mp : 0<m)
    (valid : ∀ᶠ n : ℕ in atTop,0<count n (n-h)) (lower : ∀ᶠ n in atTop,∀ z,m≤a n z)
    (direct : ∀ η>0,Tendsto (fun n => probCruceMalo n h (a n) η) atTop (𝓝 0)) :
    let w:=fun n z => 1/a n z
    (∀ ε>0,Tendsto (fun n => desviacion n (n-h) (Dobs n h (w n)) 1 ε) atTop (𝓝 0)) ∧
    Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 1) := by
  intro w
  have dev (ε : ℝ) (ep : 0<ε) :
      Tendsto (fun n => desviacion n (n-h) (Dobs n h (w n)) 1 ε) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (direct (m*ε) (mul_pos mp ep))
    · apply Eventually.of_forall; intro n; unfold desviacion
      apply Finset.sum_nonneg; intro x _; split <;> positivity
    · filter_upwards [lower,eventually_ge_atTop h] with n lo nh
      exact desviacion_por_cruces n h hh nh (a n) m ε mp lo
  refine ⟨dev,?_⟩
  have bounded : ∀ᶠ n : ℕ in atTop,∀ x∈nivel n (n-h),|Dobs n h (w n) x|≤1/m := by
    filter_upwards [lower,eventually_ge_atTop h] with n lo nh
    apply directa_acotada n h nh hh (w n) (1/m) (by positivity)
    intro z
    change |1/a n z|≤1/m
    have ap : m≤a n z := lo z
    rw [abs_of_nonneg (div_nonneg zero_le_one (mp.le.trans ap))]
    exact div_le_div_of_nonneg_left zero_le_one mp (lo z)
  exact (media_desde_prob _ _ 1 (1/m) valid bounded dev).congr
    (fun n => (directa_uniforme n h (w n)).symm)

/-- On the actual uniform layer, every empty cross is divided by its own mesh target. -/
theorem directa_ponderada_de_malla {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b)
    (ext : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0)))
    (h : ℕ) (hh : 0<h) :
    let w := fun (n : ℕ) (z : Cell n) => 1/blancoNormalizado h (p ((h:ℝ)/n)) z
    (∀ ε>0,Tendsto (fun n => desviacion n (n-h) (Dobs n h (w n)) 1 ε) atTop (𝓝 0)) ∧
    Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 1) := by
  intro w
  let a := fun (n : ℕ) => blancoNormalizado (n:=n) h (p ((h:ℝ)/n))
  let m := (κ/2)^4/2
  have pos : 0<(κ/2)^4 := pow_pos (half_pos rama.kp) _
  have mp : 0<m := half_pos pos
  obtain ⟨C,bal⟩ := balance_de_la_rama_puntual rama pt
  have lower := piso_eventual_de_las_raices rama h C (bal h) m (half_lt_self pos)
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 zero
  have first := conteo_local_implica_primer_orden (ext (admisibilidad_del_lleno full))
  have sol := soluciones_eventuales_del_primer_orden first
  have valid : ∀ᶠ n : ℕ in atTop,0<count n (n-h) := by
    filter_upwards [sol,eventually_ge_atTop h] with n s nh
    exact capa_positiva_si_hay_solucion nh s
  exact directa_ponderada_desde_cruces h hh a m mp valid lower
    (directa_de_la_rama rama h ext (fun _ => h) (Eventually.of_forall (fun _ => le_rfl)) C (bal h))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.directa_ponderada_de_malla
