import TendenciaLocal
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem mul_live (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {a b : α} (ha : a ≠ s.zero) (hb : b ≠ s.zero) : a ⊗ b ≠ s.zero := by
  intro h
  have eq := congrArg (s.mul (inv a)) h
  rw [←s.mulAssoc,recip _ ha,s.oneMul,s.mulZero] at eq
  exact hb eq

/-- Margin assumptions refer to unnormalized masses per n² or per n.
All four virtual families must be included. -/
theorem positive_rows {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, a ≼ s.zero → a = s.zero)
    (v : Cell n → α) (a l : α) (wt : ∀ e, weights s w.real (lines e) = a ⊗ v e)
    (sn : ns s n ≠ s.zero) (sa : a ≠ s.zero) (sl : l ≠ s.zero)
    (realLow : l ≼ norm s inv (ns s n ⊗ ns s n) (boardSum s v (fun e => available x (lines e))))
    (virtLow : ∀ i, l ≼ norm s inv (ns s n) (Cart.part s x w i)) :
    (((ns s n ⊗ ns s n) ⊗ a) ⊗ l) ≼ total s (realChoices s x w) ∧
    (∀ i, (ns s n ⊗ l) ≼ Cart.part s x w i) ∧
    total s (realChoices s x w) ≠ s.zero ∧ total s (virtualChoices s x w) ≠ s.zero := by
  have sq := mul_live s inv recip sn sn
  have wr : total s (realChoices s x w) = a ⊗ boardSum s v (fun e => available x (lines e)) := by
    change total s (onList (board n) _ _ Choice.real) = _
    rw [Cart.total_list]
    have h : (fun e => if available x (lines e) then weights s w.real (lines e) else s.zero) =
        fun e => (if available x (lines e) then v e else s.zero) ⊗ a := by
      funext e; cases ht : available x (lines e) <;> simp [ht,wt,s.mulComm,s.mulZero]
    rw [h,Cart.sum_scale,s.mulComm]; rfl
  have r := s.mulMono (s.refl a) (s.mulMono (s.refl (ns s n ⊗ ns s n)) realLow)
  rw [restore s inv recip sq,←wr] at r
  have ra : a ⊗ ((ns s n ⊗ ns s n) ⊗ l) = ((ns s n ⊗ ns s n) ⊗ a) ⊗ l := by ac_rfl
  rw [ra] at r
  have H (i : Fin 4) : (ns s n ⊗ l) ≼ Cart.part s x w i := by
    have h := s.mulMono (s.refl (ns s n)) (virtLow i)
    rwa [restore s inv recip sn] at h
  have live (i : Fin 4) := nonzero_of_lower s proper (mul_live s inv recip sn sl) (H i)
  refine ⟨r,H,nonzero_of_lower s proper (mul_live s inv recip (mul_live s inv recip sq sa) sl) r,?_⟩
  rw [Cart.normalizer]
  exact mul_live s inv recip (mul_live s inv recip (live 0) (live 1)) (mul_live s inv recip (live 2) (live 3))

/-- The finite error coefficient is independent of the tolerance. -/
theorem cost_linear (I M e : α) :
    cost s I M e = (I ⊗ (s.add (s.add M M) (M ⊗ M))) ⊗ e := by
  unfold cost
  rw [s.mulAssoc I,s.addMul,s.addMul,s.mulAssoc M M]

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.positive_rows
