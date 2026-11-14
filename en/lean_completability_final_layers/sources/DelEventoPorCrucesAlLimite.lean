import EstructuraDeLasMedias
open Filter
open scoped Topology BigOperators
namespace ArticuloA.Limites
open Repair
noncomputable section
open Classical

def probCruceMalo (n h : ℕ) (a : Cell n→ℝ) (η : ℝ) := ∑ p∈nivel n (n-h),
  if ∃ z∈cruces p,η < |(crossDegree (n-h) p z:ℝ)/n-a z| then (count n (n-h):ℝ)⁻¹ else 0

theorem desviacion_por_cruces (n h : ℕ) (hh : 0<h) (nh : h≤n) (a : Cell n→ℝ) (m ε : ℝ)
    (hm : 0<m) (lower : ∀ z,m≤a z) :
    desviacion n (n-h) (Dobs n h (fun z => 1/a z)) 1 ε ≤ probCruceMalo n h a (m*ε) := by
  apply Finset.sum_le_sum; intro p hp
  have pair := (Finset.mem_filter.mp hp).2
  have ncr := numero_cruces p pair.1
  rw [pair.2,show n-(n-h)=h by omega] at ncr
  have one : mediaCruces p h (fun _ => (1:ℝ))=1 := by
    simp [mediaCruces,ncr,hh.ne']
  by_cases bad : ∃ z∈cruces p,m*ε < |(crossDegree (n-h) p z:ℝ)/n-a z|
  · rw [if_pos bad]; split <;> first | exact le_rfl | positivity
  · have good (z) (mem : z∈cruces p) : |(crossDegree (n-h) p z:ℝ)/n-a z|≤m*ε :=
      le_of_not_gt (fun ex => bad ⟨z,mem,ex⟩)
    have e := error_reponderado p h hh nh pair.1 pair.2 a (fun _ => (1:ℝ)) m 1 (m*ε)
      hm lower (by simp) good
    rw [one,show 1/m*(m*ε)=ε by field_simp] at e
    simp only [bad,if_false,if_neg (not_lt_of_ge e),le_refl]

theorem limite_desde_cruces_e_inversa (h : ℕ) (hh : 0<h) (a : (n : ℕ)→Cell n→ℝ) (m b : ℝ)
    (hm : 0<m) (hb : 0<b) (lower : ∀ n z,m≤a n z)
    (lev : ∀ᶠ n in atTop,0<count n (n-h) ∧ 0<count n (n-h+1))
    (dir : ∀ η>0,Tendsto (fun n => probCruceMalo n h (a n) η) atTop (𝓝 0))
    (inv : ∀ ε>0,Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (fun z => 1/a n z)) b ε) atTop (𝓝 0)) :
    Tendsto (fun n => fracReal n h) atTop (𝓝 (1/b)) := by
  apply limite_por_eventos h hh (fun n z => 1/a n z) b (1/m) hb (by positivity) _ lev _ inv
  · intro n z
    rw [abs_of_nonneg (div_nonneg zero_le_one (hm.le.trans (lower n z)))]
    exact div_le_div_of_nonneg_left zero_le_one hm (lower n z)
  · intro ε ep
    apply squeeze_zero' _ _ (dir (m*ε) (mul_pos hm ep))
    · apply Eventually.of_forall; intro n; unfold desviacion
      apply Finset.sum_nonneg; intro p _; split <;> positivity
    · filter_upwards [eventually_ge_atTop h] with n nh
      exact desviacion_por_cruces n h hh nh (a n) m ε hm (lower n)
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.desviacion_por_cruces
#print axioms ArticuloA.Limites.limite_desde_cruces_e_inversa
