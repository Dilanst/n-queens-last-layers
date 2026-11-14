import BalanceDelPaso
import ValorDelCompensador
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte ArticuloA.Repair E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem filter_sum {ι : Type} (L : List ι) (ok : ι → Bool) (f : ι → α) :
    s.sum L (fun i => if ok i then f i else s.zero) = s.sum (L.filter ok) f := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    cases h : ok i <;> simp [MassScale.sum,List.filter_cons,h,s.zero_add] at ih ⊢ <;> rw [ih]

theorem as_dual {n} (x : State n) (z e : Cell n) (p : Fin 4 → α) (u b : α) (j : Bool) :
    signedPart s x z e p u b j = dualPart s j (coeff s p u) (fun J => b ⊗ coeff s p u J)
      (bit s true x z e) (bit s false x z e) := by
  classical
  unfold signedPart dualPart masks
  rw [←filter_sum]; apply congrArg (s.sum _); funext m
  simp only [beq_iff_eq]
  by_cases par : parity (keys m) = j
  · simp only [par,if_true,s.mulAdd]
    by_cases av : availPattern x z e m <;> simp [bit,pattern,av,s.mulOne,s.mulZero,s.mulComm b]
  · simp [par]

theorem kernel_dual {n} (row : Atoms α (State n)) (z e : Cell n) (p : Fin 4 → α) (u b : α) (j : Bool) :
    avg s row (fun y => signedPart s y z e p u b j) =
    dualPart s j (coeff s p u) (fun J => b ⊗ coeff s p u J)
      (fun m => avg s row (fun y => bit s true y z e m))
      (fun m => avg s row (fun y => bit s false y z e m)) := by
  simp only [as_dual,dualPart,avg_sum,avg_plus,avg_mul]

open Classical in
noncomputable def occError {n} (x : State n) (z e : Cell n) (m : Marks) (b d P : α) :=
  s.times 4 (if occupied x z e m then b else s.zero) ⊞
    ((if availPattern x z e m then d else s.zero) ⊞ s.times (indicator (occupied x z e m)*6) P)

open Classical in
noncomputable def avError {n} (x : State n) (z e : Cell n) (m : Marks) (b P : α) :=
  s.times 8 b ⊞ s.times (indicator (availPattern x z e m)*28) P

theorem kernel_patterns {n} {x : State n} {w : ColorWeights α} {inv : α → α}
    (A : Region s x w inv) (good : coherent x)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one) (proper : ∀ a, s.le a s.zero → a = s.zero)
    (pos : ∀ i j : Nat, i+j ≠ 0 → ns s i ⊞ ns s j ≠ s.zero)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0) (t : Nat) (z e : Cell n) :
    let size := ns s n
    let a := inv size ⊗ inv A.time
    let k := inv (size ⊗ size) ⊗ A.birth e
    let b := inv size ⊗ A.combined
    let d := inv (size ⊗ size) ⊗ A.budget
    let p := fun j => A.p (side j,key z e j)
    let Z := fun o => bit s o x z e
    let U := fun o m => avg s (kernel s w inv t x) (fun y => bit s o y z e m)
    ∀ m, ∃ P : α,
      s.le (s.times (n*n) P) ((inv A.l ⊗ A.mr) ⊞ s.times 4 (inv (s.four (fun _ => A.l)) ⊗ A.mv)) ∧
      within s ((U true m ⊞ (selfRate s true a m ⊗ Z true m)) ⊞ (a ⊗ cross s p (Z true) m))
        (Z true m ⊞ (k ⊗ Z false m)) (occError s x z e m b d P) ∧
      within s ((U false m ⊞ (selfRate s false a m ⊗ Z false m)) ⊞ (a ⊗ cross s p (Z false) m))
        (Z false m) (avError s x z e m b P) := by
  classical
  intro size a k b d p Z U m
  obtain ⟨P,cap,oc,av⟩ := A.pattern_drift good recip proper z e m
  refine ⟨P,cap,?_⟩
  let row := choices s x w inv
  have norm := choices_total s x t w inv recip pos running remain
  have past (o : Bool) : meanN s row (fun _ => indicator (pattern o x z e m)) = Z o m := by
    rw [mean_indicator_avg]; change avg s row (fun _ => Z o m) = Z o m
    rw [avg_constant]; exact (congrArg (fun v => v ⊗ Z o m) norm).trans (s.oneMul _)
  have future (o : Bool) : meanN s row (fun i => indicator (pattern o (next x i) z e m)) = U o m :=
    (expectation_next s x t w inv running remain (fun y => pattern o y z e m)).symm
  have gate : (if availPattern x z e m then k else s.zero) = k ⊗ Z false m := by
    by_cases v : availPattern x z e m <;> simp [v,Z,bit,pattern,s.mulOne,s.mulZero]
  have rateEq : (fun j => inv size ⊗ (inv A.time ⊗ p j)) = fun j => a ⊗ p j :=
    funext (fun j => (s.mulAssoc _ _ _).symm)
  change within s (_ ⊞ weightedSingles s true x z e m (referenceRate a (fun j => inv size ⊗ (inv A.time ⊗ p j)) m))
    (_ ⊞ (if availPattern x z e m then k else s.zero)) _ at oc
  change within s (_ ⊞ weightedSingles s false x z e m (referenceRate a (fun j => inv size ⊗ (inv A.time ⊗ p j)) m)) _ _ at av
  rw [rateEq,losses_in_basis,←s.assoc,gate] at oc
  rw [rateEq,losses_in_basis,←s.assoc] at av
  dsimp only [row] at past future
  dsimp only at oc av
  rw [future true,past true] at oc
  rw [future false,past false] at av
  exact ⟨oc,av⟩

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.kernel_patterns
#print axioms ArticuloA.Trayectoria.Adjunto.kernel_dual
