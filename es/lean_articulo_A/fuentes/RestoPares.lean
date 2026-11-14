import PromocionMarca
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
abbrev Both := Sum (Fin 4) (Fin 4)
def ix : Both → Fin 8
  | .inl j => ⟨j.val,by omega⟩
  | .inr j => ⟨4+j.val,by omega⟩

private theorem ix_inj (i j : Both) (eq : ix i = ix j) : i=j := by
  have h := congrArg Fin.val eq
  cases i <;> cases j <;> simp [ix] at h ⊢ <;> first | exact Fin.ext h | omega

private theorem distinct_pair {ι} (L : List ι) (nd : L.Nodup) (p : ι × ι) (hp : p ∈ pairs L) : p.1 ≠ p.2 := by
  induction L with
  | nil => simp [pairs] at hp
  | cons i L ih =>
    rcases List.mem_append.mp hp with one|tail
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp one
      intro eq; change i=j at eq
      exact (List.nodup_cons.mp nd).1 (eq.symm ▸ hj)
    · exact ih (List.nodup_cons.mp nd).2 tail

private theorem covered {n} (z e : Cell n) (m : Marks) (a : Choice n) (i : Both)
    (h : effect z e m a i) :
    consumeVertex a (vertex z e (ix i)).1 (vertex z e (ix i)).2 := by
  cases i with
  | inl j =>
    have cases4 : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases4 with rfl|rfl|rfl|rfl <;> exact h
  | inr j =>
    have cases4 : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases4 with rfl|rfl|rfl|rfl <;> exact h.1

/-- Concrete normalized atom budgets. Br bounds one real draw; Bv bounds
one virtual tuple, including its colour probability in both cases. -/
structure AtomBounds {n α} (s : ProfileScale α) (x : State n) (u : ColorWeights α) (inv : α → α) where
  realCap : α
  virtualCap : α
  realNormal : total s (realChoices s x u) ≠ s.zero
  virtualNormal : total s (virtualChoices s x u) ≠ s.zero
  capR : ∀ e, available x (lines e) → s.le (realAtom s x u inv e) realCap
  capV : ∀ g ∈ virtualEdges (2*n-1), available x g → s.le (virtAtom s x u inv g) virtualCap

namespace AtomBounds
variable {n α} {s : ProfileScale α} {x : State n} {u : ColorWeights α} {inv : α → α}
    (B : AtomBounds s x u inv)
def pairCap := s.add B.realCap (s.times ((2*n-1)*(2*n-1)) B.virtualCap)

theorem effectivePair (z e : Cell n) (G : filterG z e) (m : Marks) (i j : Both) (ne : i≠j) :
    s.le (meanN s (choices s x u inv) (fun a => indicator (effect z e m a i ∧ effect z e m a j))) B.pairCap := by
  have separate : vertex z e (ix i) ≠ vertex z e (ix j) :=
    fun eq => ne (ix_inj i j (vertices_distinct z e G _ _ eq))
  exact pair_mass s x u inv B.realNormal B.virtualNormal B.realCap B.virtualCap B.capR B.capV _ _ separate _
    (fun a h => ⟨covered z e m a i h.1,covered z e m a j h.2⟩)

theorem four_excess (z e : Cell n) (G : filterG z e) (m : Marks) :
    s.le (meanN s (choices s x u inv) (fun a => deathsOn targets (eraseDest z e m a)-1))
      (s.times 6 B.pairCap) := by
  apply exchange_bound s _ targets (fun a => eraseDest z e m a) B.pairCap
  intro ij h; have ne := distinct_pair targets (by decide) ij h
  exact B.effectivePair z e G m (.inr ij.1) (.inr ij.2) (fun eq => ne (Sum.inr.inj eq))

theorem eight_excess (z e : Cell n) (G : filterG z e) (m : Marks) :
    s.le (meanN s (choices s x u inv) (fun a => deathsOn allSlots (effect z e m a)-1))
      (s.times 28 B.pairCap) := by
  apply exchange_bound s _ allSlots (fun a => effect z e m a) B.pairCap
  intro ij h; exact B.effectivePair z e G m _ _ (distinct_pair allSlots (by decide) ij h)

end AtomBounds
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.AtomBounds.four_excess
#print axioms ArticuloA.Trayectoria.E2.AtomBounds.eight_excess
