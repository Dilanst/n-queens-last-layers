import FibrasDeRegularidad
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Corte ProfileKernel Adjunto
variable {n α} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem degree_jump (x : State n) (a : Choice n) (v : Cell n → α) (M : α)
    (cap : ∀ e, s.le (v e) M) (j : Vertex) :
    within s (auxDegree s (next x a) v j) (auxDegree s x v j) (s.times 3 M) := by
  let F := families (some j.1)
  let keep := fun e : Cell n => hitsVertex (lines e) j
  have h := gate_loss_cap s x a v keep F M cap 1 (by
    intro i hi
    have ne : j ≠ (i,lineOf a i) := by
      intro eq
      have distinct : some i ≠ some j.1 := of_decide_eq_true (List.mem_filter.mp hi).2
      exact distinct (congrArg some (congrArg Prod.fst eq).symm)
    exact real_pair_count j (i,lineOf a i) ne)
  have len : F.length = 3 := (counts (some j.1)).2.1
  rw [len,Nat.mul_one] at h
  rw [←(identities s (next x a) v j).2,←(identities s x v j).2]
  exact loss_to_jump s (mass_balance s x v keep F a) h

theorem board_mass_jump (x : State n) (a : Choice n) (v : Cell n → α) (M : α)
    (cap : ∀ e, s.le (v e) M) :
    within s (boardSum s v (fun e => available (next x a) (lines e)))
      (boardSum s v (fun e => available x (lines e))) (s.times (4*n) M) := by
  let F := families none
  have h := gate_loss_cap s x a v (fun _ => true) F M cap n (by
    intro i _; simpa only [Bool.true_and] using fiber_cap (n:=n) i (lineOf a i))
  rw [show F.length = 4 from (counts none).2.1] at h
  rw [←(identities s (next x a) v (0,0)).1,←(identities s x v (0,0)).1]
  exact loss_to_jump s (mass_balance s x v (fun _ => true) F a) h

theorem normalized_board_jump (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (sn : ns s n ≠ s.zero) (x : State n) (a : Choice n) (v : Cell n → α) (M : α)
    (cap : ∀ e, s.le (v e) M) :
    within s (norm s inv (ns s n) (boardSum s v (fun e => available (next x a) (lines e))))
      (norm s inv (ns s n) (boardSum s v (fun e => available x (lines e)))) (s.times 4 M) := by
  have h := scale s (inv (ns s n)) (board_mass_jump s x a v M cap)
  have eq : inv (ns s n) ⊗ s.times (4*n) M = s.times 4 M := by
    rw [times_m,size_mult,s.mulComm (ns s 4),s.mulAssoc,←s.mulAssoc,recip _ sn,s.oneMul,times_m]
  rwa [eq] at h

private theorem one_hit (L : List Nat) (nd : L.Nodup) (k : Nat) :
    L.countP (fun i => i == k) ≤ 1 := by
  induction L with
  | nil => simp
  | cons i L ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp nd
    rw [List.countP_cons]; by_cases h : i=k
    · subst i
      have zero : L.countP (fun i => i==k) = 0 := List.countP_eq_zero.mpr
        (fun j hj hit => absent ((beq_iff_eq.mp hit) ▸ hj))
      simp [zero]
    · simpa [h] using ih tail

theorem family_jump (x : State n) (a : Choice n) (w : ColorWeights α) (f : Fin 4)
    (B : α) (bound : ∀ j < 2*n-1, x.active f j → s.le (w f j) B) :
    within s (Cart.part s (next x a) w f) (Cart.part s x w f) B := by
  classical
  apply loss_to_jump s (family_step s x w f a)
  let L := List.range (2*n-1)
  let v := fun j => if x.active f j then w f j else s.zero
  have hh (j : Nat) : s.le
      (if x.active f j then w f j ⊗ mark s (fun a => consumeVertex a f j) a else s.zero)
      (if j == lineOf a f then v j else s.zero) := by
    by_cases h : consumeVertex a f j
    · have eq := consumed_eq a f j h
      simp only [mark,if_pos h,s.mulOne]
      simp [eq,v,s.refl]
    · cases hh : x.active f j <;> simp [hh,h,mark,s.mulZero,s.zero_le]
  have first := s.sum_mono L _ _ (fun j _ => hh j)
  have hh' := on_bits s L (fun j => j == lineOf a f) v B (by
    intro j hj _
    cases on : x.active f j <;> simp [v,on,s.zero_le,bound j (List.mem_range.mp hj)])
  have last := le_times s (one_hit L List.nodup_range (lineOf a f)) B
  apply s.trans first (s.trans hh' _)
  simpa only [MassScale.times,s.comm B s.zero,s.zero_add] using last

theorem real_quota_jump (x : State n) (a : Choice n) :
    within s (ns s (next x a).reals) (ns s x.reals) s.one := by
  cases a with
  | fail => exact within_self s _ _
  | virtual _ => exact within_self s _ _
  | real _ =>
    change within s (ns s (x.reals-1)) (ns s x.reals) s.one
    cases eq : x.reals with
    | zero => exact within_self s _ _
    | succ j =>
      have identity : ns s j ⊞ s.one = ns s (j+1) := s.comm _ _
      exact loss_to_jump s identity (s.refl _)

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.degree_jump
#print axioms ArticuloA.Trayectoria.E2.Regular.normalized_board_jump
#print axioms ArticuloA.Trayectoria.E2.Regular.family_jump
#print axioms ArticuloA.Trayectoria.E2.Regular.real_quota_jump
