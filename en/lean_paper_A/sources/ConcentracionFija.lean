import ProcesoE2

namespace ArticuloA.Trayectoria.ProfileKernel
open ArticuloA.Corte
variable {α X : Type} (s : ProfileScale α)

private theorem avg_add (xs : Atoms α X) (f g : X → α) :
    avg s xs (fun x => s.add (f x) (g x)) = s.add (avg s xs f) (avg s xs g) := by
  induction xs with
  | nil => exact (s.zero_add _).symm
  | cons v xs ih =>
    change s.add (s.mul v.1 (s.add (f v.2) (g v.2))) (avg s xs (fun x => s.add (f x) (g x))) =
      s.add (s.add _ (avg s xs f)) (s.add _ (avg s xs g))
    rw [s.mulAdd,ih,s.assoc,← s.assoc (s.mul v.1 (g v.2)),s.comm (s.mul v.1 (g v.2)) (avg s xs f),
      s.assoc,← s.assoc]

private theorem avg_const (xs : Atoms α X) (v : α) (norm : total s xs = s.one) :
    avg s xs (fun _ => v) = v := by
  have eq := avg_mul s xs v (fun _ => s.one)
  simp only [s.mulOne] at eq
  change _ = s.mul v (total s xs) at eq
  rwa [norm,s.mulOne] at eq

/-- Hoeffding chord for one row: the model input is the expectation of the
affine jump coordinate. The chord itself is a scalar inequality on each jump. -/
theorem chord_row (xs : Atoms α X) (F index : X → α) (H lo slope q : α)
    (norm : total s xs = s.one) (drift : s.le (avg s xs index) q)
    (chord : ∀ i ∈ xs, s.le (F i.2) (s.mul H (s.add lo (s.mul slope (index i.2))))) :
    s.le (avg s xs F) (s.mul (s.add lo (s.mul slope q)) H) := by
  have h := avg_mono s xs F (fun y => s.mul H (s.add lo (s.mul slope (index y)))) chord
  rw [avg_mul,avg_add,avg_const s xs lo norm,avg_mul] at h
  exact s.trans h (by rw [s.mulComm _ H]; exact s.mulMono (s.refl _) (s.mono (s.refl _) (s.mulMono (s.refl _) drift)))

/-- Before the horizon the active state includes transitions into the stopped set.
After stopping (or the deterministic horizon) both state and time are constant. -/
def freezeAt (T : Nat) (halt : Nat → X → Bool) (t : Nat) (x : X) := decide (T ≤ t) || halt t x

theorem fixed_tail (step : Nat → X → Atoms α X) (norm : ∀ t x, total s (step t x) = s.one)
    (T : Nat) (halt : Nat → X → Bool) (F : Nat → X → α) (index : Nat → X → X → α)
    (lo slope q b : α) (x₀ : X) (E : X → Prop)
    (noncontract : s.le s.one (s.add lo (s.mul slope q)))
    (drift : ∀ t < T, ∀ x, halt t x = false → s.le (avg s (step t x) (index t x)) q)
    (chord : ∀ t < T, ∀ x, halt t x = false → ∀ i ∈ step t x,
      s.le (F (t+1) i.2) (s.mul (F t x) (s.add lo (s.mul slope (index t x i.2))))) 
    (threshold : ∀ x, halt T x = false → E x → s.le s.one (s.mul b (F T x))) :
    let chain := stopped s step (freezeAt T halt)
    let bad := fun v : Nat × X => v.1 = T ∧ halt T v.2 = false ∧ E v.2
    s.le (avg s (leaves s chain 0 T (0,x₀)) (mark s bad))
      (s.mul b (s.mul (power s (s.add lo (s.mul slope q)) T) (F 0 x₀))) := by
  intro chain bad
  refine leaf_tail s chain (fun _ v => F v.1 v.2) bad _ b ?_ 0 T (0,x₀) ?_
  · intro u v
    change s.le (avg s (stopped s step (freezeAt T halt) u v) (fun y => F y.1 y.2)) _
    unfold stopped
    split
    · rw [avg_point]
      have h := s.mulMono noncontract (s.refl (F v.1 v.2))
      rwa [s.oneMul] at h
    · rename_i active
      have live : v.1 < T ∧ halt v.1 v.2 = false := by
        simpa [freezeAt, Bool.or_eq_true, Nat.not_le] using active
      rw [avg_push]
      exact chord_row s (step v.1 v.2) _ _ _ _ _ _ (norm _ _)
        (drift _ live.1 _ live.2) (chord _ live.1 _ live.2)
  · intro i _ ev
    obtain ⟨time,ok,low⟩ := ev
    change s.le s.one (s.mul b (F i.2.1 i.2.2))
    rw [time]; exact threshold _ ok low

end ArticuloA.Trayectoria.ProfileKernel
#print axioms ArticuloA.Trayectoria.ProfileKernel.chord_row
#print axioms ArticuloA.Trayectoria.ProfileKernel.fixed_tail
