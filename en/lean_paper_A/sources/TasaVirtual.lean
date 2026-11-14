import EscalaPares
namespace ArticuloA.Trayectoria.E2.Cart
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

def restricted {n} (x : State n) (v : Vertex) (i : Fin 4) (j : Nat) :=
  x.active i j && (if i=v.1 then j==v.2 else true)

theorem hit_gate {n} (x : State n) (g : Edge) (v : Vertex) :
    (available x g && hitsVertex g v) = at4 (restricted x v) g := by
  rw [active_eq]; obtain ⟨i,v⟩ := v
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hh with rfl|rfl|rfl|rfl <;> simp [at4,restricted,hitsVertex,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]

private theorem select_weight (L : List Nat) (nd : L.Nodup) (k : Nat) (f : Nat → Bool) (w : Nat → α) :
    s.sum L (fun j => if f j && (j==k) then w j else s.zero) =
    if k∈L ∧ f k then w k else s.zero := by
  induction L with
  | nil => simp [MassScale.sum]
  | cons i L ih =>
    change s.add _ (s.sum L _) = _
    rw [ih (List.nodup_cons.mp nd).2]
    by_cases h : i=k
    · subst i; cases hx : f k <;> simp_all [s.comm _ s.zero,s.zero_add]
    · simp [h,Ne.symm h,s.zero_add]

def constrainedPart {n} (x : State n) (u : ColorWeights α) (v : Vertex) (i : Fin 4) :=
  if i=v.1 then (if v.2 < 2*n-1 ∧ x.active i v.2 then u i v.2 else s.zero) else part s x u i

/-- Unnormalized weight of virtual tuples touching a vertex. The constrained
factor is its single active weight (zero when absent); the other three are U_f. -/
theorem hit_weight {n} (x : State n) (u : ColorWeights α) (v : Vertex) :
    s.sum (virtualEdges (2*n-1)) (fun g => if available x g && hitsVertex g v then weights s u g else s.zero) =
      s.four (constrainedPart s x u v) := by
  simp only [hit_gate,truncated]
  apply congrArg s.four; funext i
  by_cases eq : i=v.1
  · simp only [restricted,constrainedPart,if_pos eq]
    rw [select_weight _ _ List.nodup_range]; simp
  · simp [restricted,constrainedPart,eq,part]

theorem other_factors {n} (x : State n) (u : ColorWeights α) (v : Vertex) :
    s.mul (s.four (constrainedPart s x u v)) (part s x u v.1) =
    s.mul (s.four (part s x u)) (if v.2 < 2*n-1 ∧ x.active v.1 v.2 then u v.1 v.2 else s.zero) := by
  obtain ⟨i,v⟩ := v; have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases hh with rfl|rfl|rfl|rfl <;>
    simp [ProfileScale.four,constrainedPart,s.mulAssoc,s.mulComm,
      show ∀ a b c, s.mul a (s.mul b c) = s.mul b (s.mul a c) from
        fun a b c => by rw [←s.mulAssoc,s.mulComm a b,s.mulAssoc]]

end ArticuloA.Trayectoria.E2.Cart
#print axioms ArticuloA.Trayectoria.E2.Cart.hit_weight
#print axioms ArticuloA.Trayectoria.E2.Cart.other_factors
