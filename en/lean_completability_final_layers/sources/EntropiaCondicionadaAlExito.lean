import TransferenciaDeEvento
open scoped BigOperators
namespace ArticuloA.Entropia

/-- p is supported on a finite set S of successful trajectories. q_i/s is
the conditioned weight there; successful histories outside S may carry mass. -/
theorem condicionar_en_exito {ι : Type*} (S : Finset ι) (p q : ι → ℝ) (s : ℝ)
    (hp : ∀ i ∈ S, 0<p i) (hq : ∀ i ∈ S, 0<q i)
    (one : ∑ i ∈ S, p i = 1) (sub : ∑ i ∈ S, q i ≤ s) (hs : 0<s) (hs1 : s≤1) :
    let D := ∑ i ∈ S, p i * Real.log (p i/q i)
    let Dc := ∑ i ∈ S, p i * Real.log (p i/(q i/s))
    Dc = D+Real.log s ∧ 0 ≤ Dc ∧ Dc ≤ D ∧ Real.exp (-D) ≤ s := by
  intro D Dc
  have id : Dc = D+Real.log s := by
    have point (i) (hi : i ∈ S) : p i*Real.log (p i/(q i/s)) =
        p i*Real.log (p i/q i)+p i*Real.log s := by
      rw [Real.log_div (hp _ hi).ne' (div_pos (hq _ hi) hs).ne',
        Real.log_div (hq _ hi).ne' hs.ne',Real.log_div (hp _ hi).ne' (hq _ hi).ne']; ring
    have H := Finset.sum_congr rfl point
    simpa only [Finset.sum_add_distrib,←Finset.sum_mul,one,one_mul] using H
  have point (i) (hi : i ∈ S) : p i - q i/s ≤ p i * Real.log (p i/(q i/s)) := by
    have P := hp i hi
    have Q := div_pos (hq i hi) hs
    have H := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos Q P)) P.le
    rw [Real.log_div Q.ne' P.ne'] at H
    rw [Real.log_div P.ne' Q.ne']
    have eq : p i*(q i/s/p i-1)=q i/s-p i := by field_simp [P.ne',hs.ne']; ring
    rw [eq] at H
    linarith
  have H := Finset.sum_le_sum point
  rw [Finset.sum_sub_distrib,one,←Finset.sum_div] at H
  have norm : (∑ i ∈ S,q i)/s ≤ 1 := (div_le_one hs).mpr sub
  have lower : 0 ≤ Dc := (sub_nonneg.mpr norm).trans H
  have upper : Dc ≤ D := by rw [id]; linarith [Real.log_nonpos hs.le hs1]
  refine ⟨id,lower,upper,?_⟩
  rw [←Real.exp_log hs]
  exact Real.exp_le_exp.mpr (by linarith)
end ArticuloA.Entropia
#print axioms ArticuloA.Entropia.condicionar_en_exito
