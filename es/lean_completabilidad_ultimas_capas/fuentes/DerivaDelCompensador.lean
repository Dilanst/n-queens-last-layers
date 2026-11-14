import EsperanzaDeCanal
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte ArticuloA.Repair E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem pred_multiple (b : α) (C : Co α) (p : Fin 4 → α) (J : List (Fin 4)) :
    predecessor s (fun L => b ⊗ C L) p J = b ⊗ predecessor s C p J := by
  rw [pred_sum,pred_sum,←left_sum]; apply congrArg (s.sum _); funext e; ac_rfl

/-- One genuine E2 step at an active predecessor. No regularity is required of
the successor. The two clock equalities identify the paper and region units. -/
theorem cell_drift {n} {x : State n} {w : ColorWeights α} {inv : α → α}
    (A : Region s x w inv) (good : coherent x)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero)
    (pos : ∀ i j : Nat, i+j ≠ 0 → ns s i ⊞ ns s j ≠ s.zero)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0)
    (t N m d : Nat) (fits : d ≤ m) (step : m+1 ≤ N)
    (live : ns s m ≠ s.zero) (nextPos : ns s (m+1) ≠ s.zero)
    (floor w₀ : α) (fl : floor ≠ s.zero) (margin : s.le floor (ns s m))
    (z e : Cell n) (hp : ∀ j, s.le (A.p (side j,key z e j)) s.one)
    (timeId : inv (ns s n) ⊗ inv A.time = inv (ns s (m+1)))
    (birthId : inv (ns s n ⊗ ns s n) ⊗ A.birth e = rate s inv w₀ (m+1)) :
    let p := fun j => A.p (side j,key z e j)
    let u := ratio s inv (d+1) (m+1)
    let v := ratio s inv d m
    let old := feed s inv w₀ (d+1) (m+1)
    let new := feed s inv w₀ d m
    let C := coeff s p v
    let D := fun J => new ⊗ C J
    let b := inv (ns s n) ⊗ A.combined
    let g := inv (ns s n ⊗ ns s n) ⊗ A.budget
    let kMax := w₀ ⊗ quart s (inv floor)
    let f := fun j => avg s (kernel s w inv t x) (fun y => signedPart s y z e p v new j)
    let o := fun j => signedPart s x z e p u old j
    ∃ P : Marks → α, (∀ l, s.le (s.times (n*n) (P l))
      ((inv A.l ⊗ A.mr) ⊞ s.times 4 (inv (s.four (fun _ => A.l)) ⊗ A.mv))) ∧
      let ef := fun j => dualPart s j C D (fun l => occError s x z e l b g (P l))
        (fun l => avError s x z e l b (P l))
      let eb := fun j => s.sum (masks j) (fun l =>
        (bit s true x z e l ⊗ occupiedCap s (inv floor)) ⊞
        (bit s false x z e l ⊗ availCap s (inv floor) (ns s N ⊗ kMax) kMax))
      within s (f false ⊞ o true) (f true ⊞ o false)
        ((ef false ⊞ ef true) ⊞ (eb false ⊞ eb true)) := by
  classical
  intro p u v old new C D b g kMax f o
  have hh := kernel_patterns s A good recip proper pos running remain t z e
  dsimp only at hh
  let P := fun l => Classical.choose (hh l)
  have allH := fun l => Classical.choose_spec (hh l)
  refine ⟨P,fun l => (allH l).1,?_⟩
  intro ef eb
  dsimp only [f,o,ef,eb]
  simp only [kernel_dual]
  simp only [as_dual]
  apply paired_step s p (inv (ns s (m+1))) (rate s inv w₀ (m+1)) C D
    (coeff s p u) (fun J => old ⊗ coeff s p u J) (bit s true x z e) (bit s false x z e)
    (fun l => avg s (kernel s w inv t x) (fun y => bit s true y z e l))
    (fun l => avg s (kernel s w inv t x) (fun y => bit s false y z e l))
    (fun l => occError s x z e l b g (P l)) (fun l => avError s x z e l b (P l))
    (fun _ => occupiedCap s (inv floor)) (fun _ => availCap s (inv floor) (ns s N ⊗ kMax) kMax)
  · intro l; rw [←timeId,←birthId]; exact (allH l).2.1
  · intro l; rw [←timeId]; exact (allH l).2.2
  · intro l; exact (before_cut s inv recip N m d fits step live nextPos floor w₀ fl margin p hp l).1
  · intro l
    have adj := (before_cut s inv recip N m d fits step live nextPos floor w₀ fl margin p hp l).2.1
    dsimp only [D]
    rw [pred_multiple]
    apply adjust s adj <;> dsimp only [selfRate,Bool.false_eq_true,if_false,C,new,old,u,v] <;>
      first | ac_rfl | (congr 1 <;> first | ac_rfl | (congr 1 <;> ac_rfl))

/-- Summing cell bounds at a root uses the SAME row on both sides. -/
theorem root_drift {X ι : Type} (row : Atoms α X) (L : List ι)
    (f : X → ι → Bool → α) (o : ι → Bool → α) (err : ι → α)
    (cell : ∀ e, within s
      (avg s row (fun y => f y e false) ⊞ o e true)
      (avg s row (fun y => f y e true) ⊞ o e false) (err e)) :
    within s
      (avg s row (fun y => s.sum L (fun e => f y e false)) ⊞ s.sum L (fun e => o e true))
      (avg s row (fun y => s.sum L (fun e => f y e true)) ⊞ s.sum L (fun e => o e false))
      (s.sum L err) := by
  rw [avg_sum,avg_sum,←add_sum,←add_sum]
  exact balance_sum s L _ _ _ cell

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.cell_drift
#print axioms ArticuloA.Trayectoria.Adjunto.root_drift
