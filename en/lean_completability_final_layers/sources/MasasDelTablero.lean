import EntradasSeccionCinco
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul

/-- The mask in the auxiliary degree ignores the queried vertex's own family.
The hit test ensures the right vertex of that family. -/
def otherLive {n} (x : State n) (f : Fin 4) (g : Edge) :=
  (List.finRange 4).all (fun i => decide (i = f) || x.active i (g i))

def boardSum {n} (v : Cell n → α) (f : Cell n → Bool) :=
  s.sum (board n) (fun e => if f e then v e else s.zero)

def auxDegree {n} (x : State n) (v : Cell n → α) (j : Vertex) :=
  boardSum s v (fun e => hitsVertex (lines e) j && otherLive x j.1 (lines e))

theorem active_gate {n} (x : State n) (j : Vertex) (g : Edge) (ha : x.active j.1 j.2 = true) :
    (available x g && hitsVertex g j) = (hitsVertex g j && otherLive x j.1 g) := by
  cases hit : hitsVertex g j with
  | false => simp
  | true =>
    have eq : g j.1 = j.2 := by simpa [hitsVertex] using hit
    simp only [Bool.and_true,Bool.true_and]
    unfold available otherLive
    apply congrArg ((List.finRange 4).all)
    funext i
    by_cases h : i=j.1
    · subst i; simp [eq,ha]
    · simp [h]

private theorem pull_sum {n} (v w : Cell n → α) (a : α) (f : Cell n → Bool)
    (eq : ∀ e, w e = a ⊗ v e) : boardSum s w f = a ⊗ boardSum s v f := by
  unfold boardSum
  have h : (fun e => if f e then w e else s.zero) =
      fun e => (if f e then v e else s.zero) ⊗ a := by
    funext i; cases hi : f i <;> simp [hi,eq,s.mulComm,s.mulZero]
  rw [h,Cart.sum_scale,s.mulComm]

theorem scaled_totals {n} (x : State n) (w : ColorWeights α) (v : Cell n → α)
    (a : α) (eq : ∀ e, weights s w.real (lines e) = a ⊗ v e) (j : Vertex)
    (live : x.active j.1 j.2 = true) :
    total s (realChoices s x w) = a ⊗ boardSum s v (fun e => available x (lines e)) ∧
    realDegree s x w j = a ⊗ auxDegree s x v j := by
  constructor
  · change total s (onList (board n) _ _ Choice.real) = _
    rw [Cart.total_list]; exact pull_sum s v _ a _ eq
  · change boardSum s (fun e => weights s w.real (lines e)) _ = _
    rw [pull_sum s v _ a _ eq]
    unfold auxDegree
    exact congrArg (fun g => a ⊗ boardSum s v g) (funext (fun e => active_gate x j (lines e) live))

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.scaled_totals
