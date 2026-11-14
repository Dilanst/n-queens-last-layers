import TerminosGenerador
namespace ArticuloA.Trayectoria
open ArticuloA.Corte

def within {α} (s : ProfileScale α) (x y b : α) := s.le x (s.add y b) ∧ s.le y (s.add x b)

private theorem reorder {α} (s : ProfileScale α) (a b c d : α) :
    s.add (s.add a b) (s.add c d) = s.add (s.add a c) (s.add b d) := by
  rw [s.assoc,←s.assoc b,s.comm b c,s.assoc,←s.assoc]

theorem within_self {α} (s : ProfileScale α) (a b : α) : within s a a b := by
  have h := s.mono (s.refl a) (s.zero_le b)
  rw [s.comm a s.zero,s.zero_add] at h
  exact ⟨h,h⟩

theorem within_add {α} (s : ProfileScale α) {x y a v w b : α}
    (u : within s x y a) (z : within s v w b) : within s (s.add x v) (s.add y w) (s.add a b) := by
  have h := s.mono u.1 z.1; have k := s.mono u.2 z.2
  rw [reorder] at h; rw [reorder] at k; exact ⟨h,k⟩

theorem within_chain {α} (s : ProfileScale α) {x y z a b : α} (u : within s x y a)
    (v : within s y z b) : within s x z (s.add a b) := by
  have p := s.trans u.1 (s.mono v.1 (s.refl a))
  have q := s.trans v.2 (s.mono u.2 (s.refl b))
  rw [s.assoc,s.comm b a] at p; rw [s.assoc] at q; exact ⟨p,q⟩

theorem singles_error {n α} (s : ProfileScale α) (occ : Bool) (x : E2.State n)
    (z e : ArticuloA.Cell n) (m : E2.Marks) (r p : E2.Both → α) (b : α)
    (est : ∀ i ∈ E2.lossKeys occ, E2.guardP occ x z e m i → within s (r i) (p i) b) :
    within s (E2.weightedSingles s occ x z e m r) (E2.weightedSingles s occ x z e m p)
      (s.times (E2.lossKeys occ).length b) := by
  classical
  unfold E2.weightedSingles
  generalize hL : E2.lossKeys occ = L at *
  clear hL
  induction L with
  | nil => exact within_self s _ _
  | cons i L ih =>
    have tail := ih (fun j hj => est j (by simp [hj])) 
    have head : within s (if E2.guardP occ x z e m i then r i else s.zero)
        (if E2.guardP occ x z e m i then p i else s.zero) b := by
      split <;> rename_i h
      · simpa [h] using est i (by simp) h
      · simpa [h] using within_self s s.zero b
    exact within_add s head tail

/-- Moving the losses to the left avoids subtraction and preserves the
positive sign of the multiple-hit correction. -/
theorem compare_balance {α} (s : ProfileScale α) {new old single pred birth source exc a b c : α}
    (eq : s.add new single = s.add (s.add old birth) exc)
    (v : within s single pred a) (w : within s birth source b) (res : s.le exc c) :
    within s (s.add new pred) (s.add old source) (s.add a (s.add b c)) := by
  have shift (k : α) {y z d : α} (h : within s y z d) : within s (s.add k y) (s.add k z) d := by
    constructor
    · rw [s.assoc]; exact s.mono (s.refl k) h.1
    · rw [s.assoc]; exact s.mono (s.refl k) h.2
  have zero : within s exc s.zero c := ⟨by simpa [s.zero_add] using res,s.zero_le _⟩
  have p := shift new (show within s pred single a from ⟨v.2,v.1⟩)
  rw [eq] at p
  have rhs := within_add s (shift old w) zero
  rw [s.comm (s.add old source) s.zero,s.zero_add] at rhs
  exact within_chain s p rhs
end ArticuloA.Trayectoria
#print axioms ArticuloA.Trayectoria.compare_balance
