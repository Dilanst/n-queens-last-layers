import ValorDelCompensador
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA E2 Corte E2.Regular Control
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

theorem dilate (size a b k : α) :
    (size ⊗ size) ⊗ occupiedCap s a = occupiedCap s (size ⊗ a) ∧
    cube s size ⊗ availCap s a b k = availCap s (size ⊗ a) (size ⊗ b) ((size ⊗ size) ⊗ k) := by
  unfold occupiedCap availCap cube occupiedCap
  constructor
  · ac_rfl
  · simp only [s.mulAdd,s.addMul]; ac_rfl

private theorem caps_mono {a b k A B K : α} (ha : a ≼ A) (hb : b ≼ B) (hk : k ≼ K) :
    occupiedCap s a ≼ occupiedCap s A ∧ availCap s a b k ≼ availCap s A B K := by
  have ro := s.mulMono (s.mulMono ha ha) (s.refl (ns s 6))
  exact ⟨ro,s.mono (s.mulMono (s.mono hk (s.mulMono (s.mulMono (s.refl _) ha) hb)) (s.mulMono ha (s.refl _)))
    (s.mono (s.mulMono hb ro) (s.mulMono ro hb))⟩

theorem on_bits {ι} (L : List ι) (live : ι → Bool) (w : ι → α) (c : α)
    (each : ∀ i ∈ L, live i → w i ≼ c) :
    s.sum L (fun i => if live i then w i else s.zero) ≼ s.times (L.countP live) c := by
  induction L with
  | nil => exact s.refl _
  | cons i L ih =>
    have tail := ih (fun j hj => each j (by simp [hj]))
    cases yes : live i with
    | false => simpa only [MassScale.sum,List.foldr_cons,yes,Bool.false_eq_true,if_false,s.zero_add,List.countP_cons] using tail
    | true =>
      have both := s.mono (each i (by simp) yes) tail
      simpa only [MassScale.sum,List.foldr_cons,yes,if_true,List.countP_cons,MassScale.times] using both

/-- Absolute local discretization errors, per root/mask, summed over the
two actual supports. Multiplication by n yields a size-independent bound. -/
theorem root_error {n} (x : State n) (legal : Legal x.physical) (root : Cell n) (mask : Marks)
    (o d : Cell n → α) (a b k A B K : α)
    (ho : ∀ e ∈ board n, occBit x root mask e → o e ≼ occupiedCap s a)
    (hd : ∀ e ∈ board n, avBit x root mask e → d e ≼ availCap s a b k)
    (ha : (ns s n ⊗ a) ≼ A) (hb : (ns s n ⊗ b) ≼ B) (hk : ((ns s n ⊗ ns s n) ⊗ k) ≼ K) :
    (ns s n ⊗ (s.sum (board n) (fun e => if occBit x root mask e then o e else s.zero) ⊞
        s.sum (board n) (fun e => if avBit x root mask e then d e else s.zero))) ≼
      (occupiedCap s A ⊞ availCap s A B K) := by
  have support := step_supports x legal root mask .fail (by trivial)
  have occ := s.trans (on_bits s _ _ _ _ ho) (le_times s support.2.2.1 _)
  have av := s.trans (on_bits s _ _ _ _ hd) (le_times s support.2.2.2 _)
  have sum := s.mulMono (s.refl (ns s n)) (s.mono occ av)
  have id : ns s n ⊗ (s.times n (occupiedCap s a) ⊞ s.times (n*n) (availCap s a b k)) =
      ((ns s n ⊗ ns s n) ⊗ occupiedCap s a) ⊞ (cube s (ns s n) ⊗ availCap s a b k) := by
    rw [s.mulAdd,times_m,times_m,size_mult]; unfold cube; ac_rfl
  rw [id,(dilate s (ns s n) a b k).1,(dilate s (ns s n) a b k).2] at sum
  obtain ⟨r,v⟩ := caps_mono s ha hb hk
  exact s.trans sum (s.mono r v)

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.root_error
