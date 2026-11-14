import ComparacionGenerador
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

def bothColours (m : Marks) : Both → Bool | .inl _ => true | .inr j => m j

private theorem hit_split {n} (z e : Cell n) (m : Marks) (i : Both) (a : Choice n) :
    let v := vertex z e (ix i)
    indicator (singled z e m i a) = indicator (colourAt true v a = true) +
      (if bothColours m i then indicator (colourAt false v a = true) else 0) := by
  classical
  dsimp only; cases i with
  | inl j =>
    cases a <;> simp [indicator,singled,bothColours,colourAt,consumeVertex,hitsVertex]
  | inr j =>
    cases h : m j <;> cases a <;> simp [indicator,singled,bothColours,colourAt,consumeVertex,hitsVertex,isReal,h]

variable {α : Type} (s : ProfileScale α)
def realRate {n} (x : State n) (u : ColorWeights α) (inv : α → α) (v : Vertex) :=
  s.mul (quota s x inv x.reals) (s.mul (inv (total s (realChoices s x u))) (realDegree s x u v))
def virtRate {n} (x : State n) (u : ColorWeights α) (inv : α → α) (v : Vertex) :=
  s.mul (quota s x inv x.virtuals) (s.mul (inv (total s (virtualChoices s x u))) (s.four (Cart.constrainedPart s x u v)))

theorem measured_rate {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (z e : Cell n) (m : Marks) (i : Both) :
    let v := vertex z e (ix i)
    measured s x u inv z e m i =
      if bothColours m i then s.add (realRate s x u inv v) (virtRate s x u inv v)
      else realRate s x u inv v := by
  dsimp only
  unfold measured
  rw [funext (hit_split z e m i),mean_plus,real_rate s x u inv rr vv]
  cases h : bothColours m i <;> simp only [Bool.false_eq_true,if_false,if_true,mean_zero,
    virtual_rate s x u inv rr vv,s.comm _ s.zero,s.zero_add,realRate,virtRate]

/-- Cleared formula for the virtual hazard of one line. No independence
assertion about real placements or about the mixture of the two colours. -/
theorem virt_rate_cleared {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → s.mul (inv a) a = s.one)
    (vv : total s (virtualChoices s x u) ≠ s.zero) (v : Vertex) :
    s.mul (virtRate s x u inv v) (Cart.part s x u v.1) =
    s.mul (quota s x inv x.virtuals) (if v.2 < 2*n-1 ∧ x.active v.1 v.2 then u v.1 v.2 else s.zero) := by
  unfold virtRate
  rw [s.mulAssoc,s.mulAssoc,Cart.other_factors,← Cart.normalizer,← s.mulAssoc (inv _),recip _ vv,s.oneMul]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.measured_rate
#print axioms ArticuloA.Trayectoria.E2.virt_rate_cleared
