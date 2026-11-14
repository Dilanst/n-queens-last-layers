import Std

namespace ArticuloA.Corte

/-- First hit up to T, with T+1 reserved for no hit. The scan is chronological. -/
def firstCut (pending : Nat → Nat) (m T : Nat) : Nat :=
  (((List.range (T+1)).find? (fun t => pending t == m))).getD (T+1)

def window (N T : Nat) : List Nat :=
  (List.range (T+1)).filter (fun t => decide (N ≤ 4*t))

theorem window_mem {N T t : Nat} : t ∈ window N T ↔ t ≤ T ∧ N ≤ 4*t := by
  simp [window, Nat.lt_succ_iff]

private theorem hit_exists (p : Nat → Nat) (m T : Nat) (start : m ≤ p 0)
    (drop : ∀ t < T, p t ≤ p (t+1) + 1) (last : p T ≤ m) :
    ∃ t, t ≤ T ∧ p t = m := by
  induction T with
  | zero => exact ⟨0, Nat.le_refl _, by omega⟩
  | succ T ih =>
    by_cases earlier : p T ≤ m
    · obtain ⟨t,ht,eq⟩ := ih (fun j hj => drop j (by omega)) earlier
      exact ⟨t,by omega,eq⟩
    · have jump := drop T (by omega)
      exact ⟨T+1,Nat.le_refl _,by omega⟩

/-- Clock and rounding checks before the probabilistic union. E is an upper
bound on the endpoint colour error in units of 1/N (the case E=0 is allowed). -/
theorem clock_at_cut (p : Nat → Nat) (m N T E : Nat) (positive : 0 < N)
    (start : m ≤ p 0) (drop : ∀ t < T, p t ≤ p (t+1) + 1)
    (colour : p T * N ≤ p 0 * (N-T) + E)
    (room : p 0 * (N-T) + E ≤ m*N) (quarter : N ≤ 4*(p 0-m)) :
    firstCut p m T ∈ window N T ∧ p (firstCut p m T) = m := by
  have last := Nat.le_of_mul_le_mul_right (Nat.le_trans colour room) positive
  obtain ⟨j,hj,hit⟩ := hit_exists p m T start drop last
  have elapsed (t : Nat) (ht : t ≤ T) : p 0 ≤ p t+t := by
    induction t with
    | zero => simp
    | succ t ih =>
      have prev := ih (by omega)
      have jump := drop t (by omega)
      omega
  unfold firstCut
  cases eq : (List.range (T+1)).find? (fun t => p t == m) with
  | none =>
    have no := List.find?_eq_none.mp eq j (List.mem_range.mpr (by omega))
    simp [hit] at no
  | some t =>
    have ht := List.mem_range.mp (List.mem_of_find?_eq_some eq)
    have check := List.find?_some eq
    have good : p t = m := beq_iff_eq.mp check
    have e := elapsed t (by omega)
    change t ∈ window N T ∧ p t = m
    exact ⟨window_mem.mpr ⟨by omega,by omega⟩,good⟩

end ArticuloA.Corte
#print axioms ArticuloA.Corte.clock_at_cut
