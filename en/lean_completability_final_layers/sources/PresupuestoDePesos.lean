import CoordenadasDelEstado
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem times_m (n : Nat) (v : α) : s.times n v = ns s n ⊗ v := by
  induction n with
  | zero => simp [ns,MassScale.times,s.mulComm,s.mulZero]
  | succ n ih => change s.add v (s.times n v) = (s.add s.one (ns s n)) ⊗ v
                 rw [s.addMul,s.oneMul,ih]

theorem size_mult (i j : Nat) : ns s (i*j) = ns s i ⊗ ns s j := by
  induction i with
  | zero => rw [Nat.zero_mul]; change s.zero = s.zero ⊗ ns s j
            rw [s.mulComm,s.mulZero]
  | succ i ih =>
    rw [Nat.succ_mul,Nat.add_comm (i*j) j]
    change s.times (j+i*j) s.one = (s.add s.one (ns s i)) ⊗ ns s j
    rw [plus_times,s.addMul,s.oneMul]; exact congrArg (s.add _) ih

theorem four_mono {v w : Fin 4 → α} (h : ∀ i, v i ≼ w i) : s.four v ≼ s.four w :=
  s.mulMono (s.mulMono (h 0) (h 1)) (s.mulMono (h 2) (h 3))

theorem quota_le_one (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {n} (x : State n) (live : timeMass s x ≠ s.zero) :
    quota s x inv x.reals ≼ s.one ∧ quota s x inv x.virtuals ≼ s.one := by
  have a := up_left s (ns s x.reals) (ns s x.virtuals)
  have b := up_left s (ns s x.virtuals) (ns s x.reals)
  rw [s.comm (ns s x.virtuals) _] at b
  have cap {q} (h : ns s q ≼ timeMass s x) : quota s x inv q ≼ s.one := by
    have v := s.mulMono (s.refl (inv (timeMass s x))) h
    rwa [recip _ live] at v
  exact ⟨cap a,cap b⟩

/-- From primitive weight and mass floors to the two budgets. -/
theorem pair_from_margins {n} (x : State n) (w : ColorWeights α) (inv : α → α)
    (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (rr : total s (realChoices s x w) ≠ s.zero) (vv : total s (virtualChoices s x w) ≠ s.zero)
    (time : timeMass s x ≠ s.zero) (l a mr mv : α)
    (pos : l ≠ s.zero) (pos4 : s.four (fun _ => l) ≠ s.zero)
    (realMin : (((ns s n ⊗ ns s n) ⊗ a) ⊗ l) ≼ total s (realChoices s x w))
    (virtMin : ∀ i, (ns s n ⊗ l) ≼ Cart.part s x w i)
    (realMax : ∀ e : Cell n, available x (lines e) → weights s w.real (lines e) ≼ (a ⊗ mr))
    (virtMax : ∀ g ∈ virtualEdges (2*n-1), available x g → weights s w g ≼ mv) :
    let B := fromWeights s x w inv rr vv (a ⊗ mr) mv realMax virtMax
    s.le (s.times (n*n) B.pairCap)
      (s.add (inv l ⊗ mr) (s.times 4 (inv (s.four (fun _ => l)) ⊗ mv))) := by
  intro B
  obtain ⟨qr,qv⟩ := quota_le_one s inv recip x time
  apply regular_pair_scale s x w inv recip rr vv _ _ _ _ realMax virtMax
  · rw [times_m,size_mult]
    have cap := s.mulMono (s.refl (ns s n ⊗ ns s n)) (s.mulMono qr (s.refl (a ⊗ mr)))
    rw [s.oneMul] at cap
    apply s.trans cap
    have low := s.mulMono realMin (s.refl (inv l ⊗ mr))
    apply s.trans _ low
    have eq : ((((ns s n ⊗ ns s n) ⊗ a) ⊗ l) ⊗ (inv l ⊗ mr)) =
        ((ns s n ⊗ ns s n) ⊗ (a ⊗ mr)) ⊗ (inv l ⊗ l) := by ac_rfl
    rw [eq,recip _ pos,s.mulOne]; exact s.refl _
  · rw [times_m,size_mult,size_mult]
    have cap := s.mulMono (s.refl ((ns s n ⊗ ns s n) ⊗ (ns s n ⊗ ns s n))) (s.mulMono qv (s.refl mv))
    rw [s.oneMul] at cap
    apply s.trans cap
    have low := s.mulMono (four_mono s virtMin) (s.refl (inv (s.four (fun _ => l)) ⊗ mv))
    apply s.trans _ low
    have eq : s.four (fun _ : Fin 4 => ns s n ⊗ l) =
        ((ns s n ⊗ ns s n) ⊗ (ns s n ⊗ ns s n)) ⊗ s.four (fun _ => l) := by
      simp only [ProfileScale.four]; ac_rfl
    let t := ((ns s n ⊗ ns s n) ⊗ (ns s n ⊗ ns s n))
    let f := s.four (fun _ => l)
    have last : (t ⊗ f) ⊗ (inv f ⊗ mv) = (t ⊗ mv) ⊗ (inv f ⊗ f) := by ac_rfl
    rw [eq,last,recip _ pos4,s.mulOne]
    exact s.refl _

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.pair_from_margins
