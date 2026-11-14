import ColaDelLibro
import InnovacionesDeRegularidad
namespace ArticuloA.RealFinita
open ArticuloA ArticuloA.Trayectoria ArticuloA.Trayectoria.E2
open E2.Regular ProfileKernel Adjunto
open scoped NNReal

theorem ns_real (j : Nat) : ns masas j = (j : ℝ≥0) := by
  induction j with
  | zero => rw [Nat.cast_zero]; rfl
  | succ j ih =>
    change (1:ℝ≥0) + ns masas j = _; rw [ih,Nat.cast_succ,add_comm]

private theorem reciprocal (a : ℝ≥0) (h : a ≠ 0) : masas.mul a⁻¹ a = masas.one :=
  inv_mul_cancel₀ h
private theorem quotas (i j : Nat) (h : i+j ≠ 0) :
    masas.add (ns masas i) (ns masas j) ≠ masas.zero := by
  change ns masas i + ns masas j ≠ 0
  rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast h

theorem cola_coordenada (E : Momento.Exponencial) {n : ℕ} (hn : n ≠ 0) (w : ColorWeights ℝ≥0)
    (v : Cell n → ℝ≥0) (halt : Nat → State n → Bool) (c : Coord) (M H : ℝ≥0)
    (cap : ∀ e, v e ≤ M)
    (line : ∀ t (x : State n), halt t x = false → ∀ f j, j < 2*n-1 → x.active f j → w f j ≤ H)
    (m : ℕ) (init : HistoryBook (Nat × State n) ℝ≥0)
    (θ a : ℝ) (positive : 0 ≤ θ) (small : θ*(2*(coordCap masas M H c).val) ≤ 1) :
    let S := stopped masas (kernel masas w (·⁻¹)) halt
    let F := fun (_ : Nat) (v₁ : Nat × State n) => observed masas (·⁻¹) v w v₁.2 c
    let B := coordCap masas M H c + coordCap masas M H c
    (avg masas (leaves masas (historyRow masas S F (fun _ _ => 0)) 0 m init)
      (mark masas (fun j => a ≤ saldo j))).val ≤
      E.fn ((m:ℝ)*(θ*B)^2 + θ*saldo init - θ*a) := by
  intro S F B
  have sn : ns masas n ≠ masas.zero := by rw [ns_real]; change (n:ℝ≥0) ≠ 0; exact_mod_cast hn
  refine cola_libro E S F (fun _ _ => 0) (stopped_total masas _ halt (kernel_total masas w _ reciprocal quotas)) B
    (fun _ => True) (by simp) ?_ 0 m init trivial θ a positive ?_
  · intro t x _ i hi
    obtain ⟨clock,state⟩ := x
    have hj := coord_stopped masas _ reciprocal quotas sn v w halt t clock state M H cap
      (line clock state) c i hi
    have eq : avg masas (S t (clock,state)) (fun _ => (0:ℝ≥0)) = 0 := by
      rw [E2.avg_constant]; exact mul_zero _
    simpa only [F,eq,add_zero,zero_add] using hj
  · change θ*((coordCap masas M H c).val + (coordCap masas M H c).val) ≤ 1
    simpa [two_mul] using small
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola_coordenada
