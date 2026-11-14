import DerivaVirtualRegional
namespace ArticuloA.Trayectoria.E2.Regular
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {n α} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

def allLive (x : State n) (e : Cell n) (F : List (Fin 4)) := ∀ i ∈ F, x.active i (lines e i) = true
def breaks (a : Choice n) (e : Cell n) (F : List (Fin 4)) := ∃ i ∈ F, consumeVertex a i (lines e i)

theorem gate_next (x : State n) (e : Cell n) (F : List (Fin 4)) (a : Choice n) :
    allLive (next x a) e F ↔ allLive x e F ∧ ¬ breaks a e F := by
  have update (i) : (next x a).active i (lines e i) = true ↔
      x.active i (lines e i) = true ∧ ¬ consumeVertex a i (lines e i) := by
    cases a <;> simp [next,consume,consumeVertex,ne_comm]
  constructor
  · intro h; exact ⟨fun i hi => (update i |>.mp (h i hi)).1,fun ⟨i,hi,hit⟩ => (update i |>.mp (h i hi)).2 hit⟩
  · rintro ⟨h,no⟩ i hi; exact (update i).mpr ⟨h i hi,fun hit => no ⟨i,hi,hit⟩⟩

theorem forbid_duplicate {ι} (F : List ι) (nd : F.Nodup) {ij : ι × ι} (hi : ij ∈ pairs F) : ij.1 ≠ ij.2 := by
  induction F with
  | nil => simp [pairs] at hi
  | cons i F ih =>
    rcases List.mem_append.mp hi with first|rest
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp first
      change i ≠ j; intro eq; exact (List.nodup_cons.mp nd).1 (eq.symm ▸ hj)
    · exact ih (List.nodup_cons.mp nd).2 rest

theorem gate_rate (x : State n) (w : ColorWeights α) (inv : α → α) (B : AtomBounds s x w inv)
    (e : Cell n) (F : List (Fin 4)) (nd : F.Nodup) (a b : α)
    (single : ∀ i ∈ F, within s (realRate s x w inv (i,lines e i) ⊞ virtRate s x w inv (i,lines e i)) a b) :
    within s (avg s (choices s x w inv) (mark s (fun k => breaks k e F))) (s.times F.length a)
      (s.add (s.times (pairs F).length B.pairCap) (s.times F.length b)) := by
  classical
  let row := choices s x w inv
  let hit := fun (k : Choice n) (i : Fin 4) => consumeVertex k i (lines e i)
  let count := fun k => deathsOn F (hit k)
  have balance (k : Choice n) : indicator (breaks k e F) + (count k - 1) = count k := by
    have eq : count k = 0 ↔ ¬ breaks k e F := by simp [count,deathsOn,List.countP_eq_zero,hit,breaks]
    by_cases h : breaks k e F
    · have nz : count k ≠ 0 := fun hc => eq.mp hc h
      simp only [indicator,if_pos h]; omega
    · simp [indicator,h,eq.mpr h]
  have identity := mean_eq s row (fun k => indicator (breaks k e F) + (count k - 1)) count (fun j _ => balance j.2)
  rw [mean_plus,mean_indicator_avg] at identity
  have over := exchange_bound s row F hit B.pairCap (by
    intro ij ijMem
    have ne : (ij.1,lines e ij.1) ≠ (ij.2,lines e ij.2) := fun h => forbid_duplicate F nd ijMem (congrArg Prod.fst h)
    exact pair_mass s x w inv B.realNormal B.virtualNormal B.realCap B.virtualCap B.capR B.capV _ _ ne _ (fun _ h => h))
  have total (L : List (Fin 4)) (sub : ∀ i ∈ L, i ∈ F) :
      within s (meanN s row (fun k => deathsOn L (hit k))) (s.times L.length a) (s.times L.length b) := by
    induction L with
    | nil => rw [show (fun k => deathsOn [] (hit k)) = fun _ => 0 from rfl,mean_zero]; exact within_self s _ _
    | cons i L ih =>
      have eq (k : Choice n) : deathsOn (i::L) (hit k) = indicator (hit k i) + deathsOn L (hit k) := by
        by_cases h : hit k i <;> simp [deathsOn,List.countP_cons,indicator,h,Nat.add_comm]
      rw [funext eq,mean_plus,mean_indicator_avg,vertex_rate s x w inv (i,lines e i) B.realNormal B.virtualNormal]
      exact within_add s (single i (sub _ (by simp))) (ih (fun j hj => sub _ (by simp [hj])))
  have base := total F (fun _ h => h)
  apply within_chain s _ base
  change within s _ (meanN s row count) _
  rw [←identity]
  generalize avg s row (mark s (fun k => breaks k e F)) = v
  constructor
  · exact s.trans (up_left s _ _) (up_left s _ _)
  · exact s.mono (s.refl _) over

end ArticuloA.Trayectoria.E2.Regular
#print axioms ArticuloA.Trayectoria.E2.Regular.gate_rate
