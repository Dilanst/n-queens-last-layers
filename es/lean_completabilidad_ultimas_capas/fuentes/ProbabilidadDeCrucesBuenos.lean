import DelEventoPorCrucesAlLimite
import DobleCuentaReal
open Filter
open scoped Topology BigOperators
namespace ArticuloA.Limites
open Repair
noncomputable section
open Classical
open private sumaNat in cardinal_nivel

def todosCerca {n} (h : ℕ) (a : Cell n→ℝ) (η : ℝ) (p : Placement n) :=
  ¬ ∃ z∈cruces p,η < |(crossDegree (n-h) p z:ℝ)/n-a z|

theorem complemento_del_fallo {n h} (pos : 0<count n (n-h)) (a : Cell n→ℝ) (η : ℝ) :
    probBuena n h (todosCerca h a η)+probCruceMalo n h a η=1 := by
  let G:=todosCerca h a η
  have card : eventCount h G=∑ p∈nivel n (n-h),if G p then 1 else 0 := by
    unfold eventCount nivel
    rw [sumaNat,Finset.sum_filter]
    apply Finset.sum_congr rfl; intro p _
    by_cases g : G p <;> by_cases lev : Legal p ∧ pieces p=n-h <;> simp [g,layer,lev]
  change (eventCount h G:ℝ)/(count n (n-h):ℝ)+_=1
  rw [card,Nat.cast_sum,Finset.sum_div]
  unfold probCruceMalo
  rw [←Finset.sum_add_distrib]
  calc _ = ∑ _∈nivel n (n-h),(count n (n-h):ℝ)⁻¹ := by
          apply Finset.sum_congr rfl; intro p _
          by_cases bad : ∃ z∈cruces p,η < |(crossDegree (n-h) p z:ℝ)/n-a z| <;>
            simp [G,todosCerca,bad,one_div]
       _ = 1 := by simp only [Finset.sum_const,cardinal_nivel,nsmul_eq_mul]
                   exact mul_inv_cancel₀ (by exact_mod_cast pos.ne')

theorem positividad_desde_malla (h : ℕ) (hh : 0<h) (a : (n : ℕ)→Cell n→ℝ)
    (piso : ℝ) (hp : 0<piso) (nonempty : ∀ᶠ n in atTop,0<count n (n-h))
    (lower : ∀ᶠ n : ℕ in atTop,∀ z,piso≤a n z)
    (directa : ∀ η>0,Tendsto (fun n => probCruceMalo n h (a n) η) atTop (𝓝 0)) :
    ∀ l<piso,∀ᶠ n in atTop,l<fracReal n h := by
  intro l hl
  let γ:ℝ:=(max 0 l+piso)/2
  have base : max 0 l < piso := max_lt hp hl
  have gp : 0<γ := by dsimp [γ]; linarith [le_max_left (0:ℝ) l]
  have gl : l<γ := by dsimp [γ]; linarith [le_max_right (0:ℝ) l]
  have ep : 0<piso-γ := by dsimp [γ]; linarith
  let η:=piso-γ
  let G:=(fun n => todosCerca h (a n) η)
  apply positividad_tipica h hh γ gp G nonempty _ _ l gl
  · filter_upwards [lower,eventually_gt_atTop 0] with n b np
    intro p _ _ good z empty
    have mem : z∈cruces p := Finset.mem_filter.mpr ⟨Finset.mem_univ _,empty⟩
    have dev : |(crossDegree (n-h) p z:ℝ)/n-a n z|≤η :=
      le_of_not_gt (fun ht => good ⟨z,mem,ht⟩)
    have one:= (abs_le.mp dev).1
    apply (le_div_iff₀ (by exact_mod_cast np : 0<(n:ℝ))).mp
    dsimp [η] at one
    linarith [b z]
  · have cv := (tendsto_const_nhds (x:= (1:ℝ))).sub (directa η ep)
    apply (show Tendsto (fun n => 1-probCruceMalo n h (a n) η) atTop (𝓝 1) by simpa using cv).congr'
    filter_upwards [nonempty] with n pos
    linarith only [complemento_del_fallo pos (a n) η]
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.positividad_desde_malla
