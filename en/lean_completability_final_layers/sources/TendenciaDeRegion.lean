import DerivaSoportes
import CuatroLineas
namespace ArticuloA.Trayectoria.E2.Regular.Region
open ArticuloA ArticuloA.Corte ProfileKernel Adjunto Control
variable {n α} {s : ProfileScale α} {x : State n} {w : ColorWeights α} {inv : α → α}
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

theorem supports_drift (A : Region s x w inv) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (proper : ∀ a, s.le a s.zero → a = s.zero) :
    let a := inv (ns s n) ⊗ inv A.time
    let b := inv (ns s n) ⊗ A.combined
    ∃ P : α, s.le (s.times (n*n) P) ((inv A.l ⊗ A.mr) ⊞ s.times 4 (inv (s.four (fun _ => A.l)) ⊗ A.mv)) ∧
      ∀ (keep : Cell n → Bool) (o : Option (Fin 4)),
      let F := families o
      let mass := massGate s x A.v keep F
      within s (avg s (choices s x w inv) (lostGate s x A.v keep F))
        (mass ⊗ s.times (if o.isSome then 3 else 4) a)
        (mass ⊗ (s.times (if o.isSome then 3 else 6) P ⊞ s.times (if o.isSome then 3 else 4) b)) := by
  intro a b
  obtain ⟨realMin,virtMin,rr,vv⟩ := A.raw_floors recip proper
  have raw (e : Cell n) (_ : available x (lines e) = true) :
      s.le (weights s w.real (lines e)) (A.common ⊗ A.mr) := by rw [A.wt]; exact s.mulMono (s.refl _) (A.weightMax e)
  have pos := mul_live s inv recip A.floorPos A.floorPos
  have pos4 : s.four (fun _ => A.l) ≠ s.zero := mul_live s inv recip pos pos
  let B := fromWeights s x w inv rr vv (A.common ⊗ A.mr) A.mv raw A.tupleMax
  refine ⟨B.pairCap,pair_from_margins s x w inv recip rr vv A.running A.l A.common A.mr A.mv
    A.floorPos pos4 realMin virtMin raw A.tupleMax,?_⟩
  intro keep o F mass
  obtain ⟨nd,len,pair⟩ := counts o
  have h := mass_trend s x A.v keep F w inv B nd a b (by
    intro e live i hi
    have on : activeLine x (i,lines e i) := ⟨on_board e i,live i hi⟩
    exact drop_scale s inv recip A.sizePos (A.estimates recip proper _ on e).2.2.1)
  change F.length = _ at len
  change (pairs F).length = _ at pair
  dsimp only at h; rw [len,pair] at h
  exact h

/-- Compare to the decrement of a moving power target; j=1 is exact,
and j=3 or 4 has a deterministic curvature error. -/
theorem target_decrement (r a X target loss E noise : α) (k : Nat)
    (time : r ⊞ a = s.one) (localEst : within s loss (s.times k a ⊗ X) noise)
    (track : within s X target E) :
    within s loss (target ⊗ (a ⊗ geom s r k))
      (noise ⊞ (((s.times k a) ⊗ E) ⊞ (target ⊗ ((a ⊗ a) ⊗ ns s (pairsN k))))) := by
  have rle := time ▸ up_left s r a
  have bound := (size_geom s r rle k).2.2
  have small := s.mulMono (s.refl (a ⊗ a)) bound
  have id : (a ⊗ geom s r k) ⊞ ((a ⊗ a) ⊗ lag s r k) = s.times k a := by
    rw [s.mulAssoc,←s.mulAdd,missing s r a time,times_m,s.mulComm]
  have shift : within s (s.times k a) (a ⊗ geom s r k) ((a ⊗ a) ⊗ ns s (pairsN k)) := by
    rw [←id]
    exact ⟨s.mono (s.refl _) small,s.trans (up_left s _ _) (up_left s _ _)⟩
  have first := scale s (s.times k a) track
  have last := scale s target shift
  rw [s.mulComm (s.times k a) target] at first
  exact within_chain s localEst (within_chain s first last)

end ArticuloA.Trayectoria.E2.Regular.Region
#print axioms ArticuloA.Trayectoria.E2.Regular.Region.supports_drift
#print axioms ArticuloA.Trayectoria.E2.Regular.Region.target_decrement
