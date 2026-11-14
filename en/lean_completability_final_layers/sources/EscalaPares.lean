import ProductoVirtual
namespace ArticuloA.Trayectoria.E2
open ArticuloA.Corte
namespace AtomBounds
variable {α n} {s : ProfileScale α} {x : State n} {u : ColorWeights α} {inv : α → α}
    (B : AtomBounds s x u inv)

private theorem times_times (s : ProfileScale α) (i j : Nat) (v : α) :
    s.times i (s.times j v) = s.times (i*j) v := by
  induction i with
  | zero => simp [MassScale.times]
  | succ i ih =>
    rw [Nat.succ_mul,Nat.add_comm (i*j),plus_times s j (i*j) v]
    exact congrArg (s.add _) ih

private theorem times_weight (s : ProfileScale α) (i : Nat) {v w : α} (h : s.le v w) :
    s.le (s.times i v) (s.times i w) := by
  induction i with | zero => exact s.refl _ | succ i ih => exact s.mono h ih

private theorem times_add (s : ProfileScale α) (i : Nat) (v w : α) :
    s.times i (s.add v w) = s.add (s.times i v) (s.times i w) := by
  induction i with
  | zero => exact (s.zero_add _).symm
  | succ i ih =>
    change s.add (s.add v w) (s.times i _) = s.add (s.add v _) (s.add w _)
    rw [ih,s.assoc,← s.assoc w,s.comm w _,s.assoc,← s.assoc]

/-- Denominator-cleared O(n^-2) from O(n^-2) real and O(n^-4) virtual atom masses. -/
theorem scaledPair (Cr Cv : α) (realScale : s.le (s.times (n*n) B.realCap) Cr)
    (virtScale : s.le (s.times ((n*n)*(n*n)) B.virtualCap) Cv) :
    s.le (s.times (n*n) B.pairCap) (s.add Cr (s.times 4 Cv)) := by
  have h : 2*n-1 ≤ 2*n := by omega
  have size := Nat.mul_le_mul_left (n*n) (Nat.mul_le_mul h h)
  have fac : (n*n)*((2*n)*(2*n)) = 4*((n*n)*(n*n)) := by
    change _ = (2*2)*_; ac_rfl
  rw [fac] at size
  rw [pairCap,times_add,times_times]
  apply s.mono realScale
  apply s.trans (le_times s size _)
  rw [←times_times]; exact times_weight s 4 virtScale

theorem avg_scale (ks : Nat) (w C : α) (h : s.le w (s.times ks B.pairCap))
    (unit : s.le (s.times (n*n) B.pairCap) C) :
    s.le (s.times (n*n) w) (s.times ks C) := by
  apply s.trans (times_weight s (n*n) h)
  rw [times_times,Nat.mul_comm,←times_times]; exact times_weight s ks unit

end AtomBounds
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.AtomBounds.scaledPair
