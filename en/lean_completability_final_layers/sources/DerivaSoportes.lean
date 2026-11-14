import TasaDeCasilla
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {n α} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

open Classical in
noncomputable def massGate (x : State n) (v : Cell n → α) (keep : Cell n → Bool) (F : List (Fin 4)) :=
  s.sum (board n) (fun e => if keep e = true ∧ allLive x e F then v e else s.zero)
open Classical in
noncomputable def lostGate (x : State n) (v : Cell n → α) (keep : Cell n → Bool) (F : List (Fin 4)) (k : Choice n) :=
  s.sum (board n) (fun e => if keep e = true ∧ allLive x e F then
    v e ⊗ mark s (fun k => breaks k e F) k else s.zero)

theorem mass_balance (x : State n) (v : Cell n → α) (keep : Cell n → Bool) (F : List (Fin 4)) (k : Choice n) :
    massGate s (next x k) v keep F ⊞ lostGate s x v keep F k = massGate s x v keep F := by
  classical
  unfold massGate lostGate
  generalize board n = L
  induction L with
  | nil => exact s.zero_add _
  | cons e L ih =>
    change (_ ⊞ s.sum L _) ⊞ (_ ⊞ s.sum L _) = _ ⊞ s.sum L _
    rw [s.assoc,←s.assoc (s.sum L _),s.comm (s.sum L _) _,s.assoc _ (s.sum L _),ih,←s.assoc]
    apply congrArg (fun y => y ⊞ _)
    dsimp only; simp only [gate_next]
    by_cases eligible : keep e = true ∧ allLive x e F <;> by_cases killed : breaks k e F <;>
      simp_all [mark,s.mulZero,s.mulOne,s.zero_add,s.comm _ s.zero]

theorem mass_trend (x : State n) (v : Cell n → α) (keep : Cell n → Bool) (F : List (Fin 4))
    (w : ColorWeights α) (inv : α → α) (B : AtomBounds s x w inv) (nd : F.Nodup)
    (a b : α) (one : ∀ e, allLive x e F → ∀ i ∈ F,
      within s (realRate s x w inv (i,lines e i) ⊞ virtRate s x w inv (i,lines e i)) a b) :
    let mass := massGate s x v keep F
    within s (avg s (choices s x w inv) (lostGate s x v keep F))
      (mass ⊗ s.times F.length a)
      (mass ⊗ (s.times (pairs F).length B.pairCap ⊞ s.times F.length b)) := by
  classical
  dsimp only
  unfold lostGate massGate
  rw [avg_sum,←Cart.sum_scale,←Cart.sum_scale]
  generalize board n = L
  induction L with
  | nil => exact within_self s _ _
  | cons i L ih =>
    apply within_add s _ ih
    by_cases gate : keep i = true ∧ allLive x i F
    · simp only [if_pos gate,avg_mul]
      exact scale s _ (gate_rate s x w inv B i F nd a b (one i gate.2))
    · have zero (v : α) : s.zero ⊗ v = s.zero := by rw [s.mulComm,s.mulZero]
      simp only [if_neg gate,avg_constant,s.mulZero,zero]
      exact within_self s _ _

def families (ignored : Option (Fin 4)) := (List.finRange 4).filter (fun i => decide (some i ≠ ignored))
theorem counts (o : Option (Fin 4)) : (families o).Nodup ∧
    (families o).length = (if o.isSome then 3 else 4) ∧
    (pairs (families o)).length = (if o.isSome then 3 else 6) := by
  cases o with
  | none => decide
  | some j =>
    have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases h with rfl|rfl|rfl|rfl <;> decide

theorem identities (x : State n) (v : Cell n → α) (j : Vertex) :
    massGate s x v (fun _ => true) (families none) = boardSum s v (fun e => available x (lines e)) ∧
    massGate s x v (fun e => hitsVertex (lines e) j) (families (some j.1)) = auxDegree s x v j := by
  classical
  have mem (i : Fin 4) : i ∈ List.finRange 4 := by simp [List.finRange,List.mem_ofFn] <;> omega
  constructor
  · apply congrArg (s.sum (board n)); funext e
    simp [available,families,allLive,List.all_eq_true,mem]
  · apply congrArg (s.sum (board n)); funext e
    have eq : allLive x e (families (some j.1)) ↔ otherLive x j.1 (lines e) = true := by
      unfold allLive families otherLive
      simp only [List.mem_filter,mem,true_and,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true]
      constructor
      · intro h i _
        by_cases hi : i=j.1
        · exact Or.inl hi
        · exact Or.inr (h i (by simpa using hi))
      · intro h i hi
        exact (h i trivial).resolve_left (by simpa using hi)
    simp [eq]

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.mass_trend
#print axioms ArticuloA.Trayectoria.E2.Regular.identities
