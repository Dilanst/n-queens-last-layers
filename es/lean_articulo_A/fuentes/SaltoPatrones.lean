import MargenPerfil

namespace ArticuloA.Trayectoria
open ArticuloA.Corte

/-- Values may be signed. Distances and error budgets live in the nonnegative scale. -/
structure SizeOn (V β : Type) (s : MassScale β) where
  zero : V
  add : V → V → V
  dist : V → V → β
  self : ∀ v, dist v v = s.zero
  symm : ∀ v w, dist v w = dist w v
  triangle : ∀ v w u, s.le (dist v u) (s.add (dist v w) (dist w u))
  addBound : ∀ v w u t, s.le (dist (add v w) (add u t)) (s.add (dist v u) (dist w t))

namespace SizeOn
variable {V β ι : Type} {s : MassScale β} (g : SizeOn V β s)
def gate (onBit : Bool) (v : V) := if onBit then v else g.zero
def score (entries : List ι) (onBit : ι → Bool) (coeff : ι → V) : V :=
  entries.foldr (fun i a => g.add (g.gate (onBit i) (coeff i)) a) g.zero

/-- If an indicator changes, pay the magnitude of the arriving coefficient once.
For an old active entry also pay the time-change of its coefficient. -/
theorem entry_jump (p q : Bool) (v w : V) (J D : β)
    (mag : p ≠ q → s.le (g.dist w g.zero) J) (variation : p = true → s.le (g.dist v w) D) :
    s.le (g.dist (g.gate p v) (g.gate q w))
      (s.add (if p != q then J else s.zero) (if p then D else s.zero)) := by
  cases p <;> cases q
  · simp [gate,g.self,s.zero_add,s.refl]
  · simpa [gate,s.comm J s.zero,s.zero_add,g.symm g.zero w] using mag (by decide)
  · have eq := s.trans (g.triangle v w g.zero) (s.mono (variation rfl) (mag (by decide)))
    simpa [gate,s.comm D J] using eq
  · simpa [gate,s.zero_add] using variation rfl

def budget (entries : List ι) (old new : ι → Bool) (J D : β) : β :=
  s.sum entries (fun i => s.add (if old i != new i then J else s.zero)
    (if old i then D else s.zero))

theorem block_jump (entries : List ι) (old new : ι → Bool) (c c' : ι → V) (J D : β)
    (mag : ∀ i ∈ entries, old i ≠ new i → s.le (g.dist (c' i) g.zero) J)
    (variation : ∀ i ∈ entries, old i = true → s.le (g.dist (c i) (c' i)) D) :
    s.le (g.dist (g.score entries old c) (g.score entries new c'))
      (budget (s := s) entries old new J D) := by
  induction entries with
  | nil => change s.le (g.dist g.zero g.zero) s.zero; rw [g.self]; exact s.refl _
  | cons i es ih =>
    apply s.trans (g.addBound _ _ _ _)
    exact s.mono (g.entry_jump _ _ _ _ _ _ (mag i (by simp)) (variation i (by simp)))
      (ih (fun j hj => mag j (by simp [hj])) (fun j hj => variation j (by simp [hj])))

def repeatMass (i : Nat) (v : β) : β :=
  match i with
  | 0 => s.zero
  | j+1 => s.add v (repeatMass j v)

theorem budget_counts (entries : List ι) (old new : ι → Bool) (J D : β) :
    budget (s := s) entries old new J D =
      s.add (repeatMass (s := s) (entries.countP (fun i => old i != new i)) J)
        (repeatMass (s := s) (entries.countP old) D) := by
  induction entries with
  | nil => exact (s.zero_add _).symm
  | cons i es ih =>
    change s.add (s.add _ _) (budget es old new J D) = _
    rw [ih,List.countP_cons,List.countP_cons]
    cases h : old i <;> cases h' : new i <;>
      simp [h,h',repeatMass,s.zero_add,s.comm J s.zero,s.assoc]
    all_goals first | rw [← s.assoc D,s.comm D _,s.assoc] | skip

end SizeOn
end ArticuloA.Trayectoria
#print axioms ArticuloA.Trayectoria.SizeOn.block_jump
#print axioms ArticuloA.Trayectoria.SizeOn.budget_counts
