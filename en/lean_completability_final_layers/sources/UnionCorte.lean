import RelojCorte
import MargenPerfil
import PerdidaCorte

namespace ArticuloA.Corte
namespace MassScale
variable {α Ω : Type} (s : MassScale α)

open Classical in
/-- Unnormalized event mass on a finite list of trajectories. With weights summing to one
this is the probability under that law. Individual atoms need not have equal weights. -/
noncomputable def mass (paths : List Ω) (weight : Ω → α) (E : Ω → Prop) :=
  s.sum paths (fun w => if E w then weight w else s.zero)

theorem mass_mono (L : List Ω) (w : Ω → α) {P Q : Ω → Prop} (incl : ∀ x, P x → Q x) :
    s.le (s.mass L w P) (s.mass L w Q) := by
  apply s.sum_mono
  intro x _
  by_cases p : P x
  · simp only [if_pos p, if_pos (incl x p)]; exact s.refl _
  · simp only [if_neg p]; exact s.zero_le _

private theorem sum_add {ι} (L : List ι) (a b : ι → α) :
    s.sum L (fun i => s.add (a i) (b i)) = s.add (s.sum L a) (s.sum L b) := by
  induction L with
  | nil => exact (s.zero_add _).symm
  | cons i L ih =>
    change s.add (s.add _ _) (s.sum L _) = s.add (s.add _ (s.sum L a)) (s.add _ (s.sum L b))
    rw [ih,s.assoc,← s.assoc (b i),s.comm (b i) (s.sum L a),s.assoc,← s.assoc]

private theorem mass_or (L : List Ω) (w : Ω → α) (P Q : Ω → Prop) :
    s.le (s.mass L w (fun x => P x ∨ Q x)) (s.add (s.mass L w P) (s.mass L w Q)) := by
  classical
  unfold mass
  rw [← s.sum_add]
  apply s.sum_mono
  intro x _
  by_cases p : P x
  · simp only [if_pos p, if_pos (Or.inl p : P x ∨ Q x)]
    have h := s.mono (s.refl (w x)) (s.zero_le (if Q x then w x else s.zero))
    rwa [s.comm (w x) s.zero,s.zero_add] at h
  · by_cases q : Q x <;> simp [p,q,s.zero_add,s.refl]

def times (k : Nat) (a : α) : α :=
  match k with
  | 0 => s.zero
  | j+1 => s.add a (times j a)

theorem union_budget {ι : Type} (L : List Ω) (w : Ω → α) (keys : List ι)
    (E : ι → Ω → Prop) (b : α) (bounds : ∀ i ∈ keys, s.le (s.mass L w (E i)) b) :
    s.le (s.mass L w (fun x => ∃ i ∈ keys, E i x)) (s.times keys.length b) := by
  induction keys with
  | nil =>
    have zeroMass (xs : List Ω) : s.sum xs (fun _ => s.zero) = s.zero := by
      induction xs with
      | nil => rfl
      | cons x xs ih => change s.add s.zero _ = _; rw [s.zero_add]; exact ih
    simpa [mass,zeroMass,times] using s.refl s.zero
  | cons i keys ih =>
    have incl (x : Ω) (h : ∃ j ∈ i::keys, E j x) : E i x ∨ ∃ j ∈ keys, E j x := by
      obtain ⟨j,mem,ej⟩ := h
      rcases List.mem_cons.mp mem with rfl | rest
      · exact .inl ej
      · exact .inr ⟨j,rest,ej⟩
    exact s.trans (s.mass_mono L w incl) (s.trans (s.mass_or _ _ _ _)
      (s.mono (bounds i (by simp)) (ih (fun j hj => bounds j (by simp [hj])))))

end MassScale

open ArticuloA.Repair

private theorem board_size (n : Nat) : (board n).length = n*n := by
  unfold board
  have rows (xs : List (Fin n)) :
      (xs.flatMap (fun r => (List.finRange n).map (fun c => (r,c)))).length = xs.length*n := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  rw [rows,List.length_finRange]

def rootTimes (N T n : Nat) := (window N T).flatMap (fun t => (board n).map (fun z => (t,z)))

theorem rootTimes_size (N T n : Nat) :
    (rootTimes N T n).length = (window N T).length * (n*n) := by
  have size (xs : List Nat) :
      (xs.flatMap (fun t => (board n).map (fun z => (t,z)))).length = xs.length * (n*n) := by
    induction xs with
    | nil => simp
    | cons t xs ih => simp [ih,board_size,Nat.succ_mul,Nat.add_comm]
  exact size _

/-- The bad event includes a missing cut, a cut outside the window, or any root
below the seed. Only deviations on paths still regular at deterministic time t
are charged. The global exceptional event is charged just once. -/
theorem random_cut_bound {α Ω : Type} (s : ProfileScale α) (L : List Ω) (w : Ω → α)
    (n m N T : Nat) (pending : Ω → Nat → Nat) (place : Ω → Nat → Placement n)
    (sigma : Ω → Nat) (exceptional : Ω → Prop)
    (center : Nat → Cell n → α) (target exitBudget tailBudget : α)
    (regular : ∀ x, ¬exceptional x →
      firstCut (pending x) m T ∈ window N T ∧ T < sigma x)
    (margin : ∀ t ∈ window N T, ∀ z, s.le (s.add target target) (center t z))
    (exitBound : s.le (s.mass L w exceptional) exitBudget)
    (fixed : ∀ t ∈ window N T, ∀ z, s.le (s.mass L w (fun x =>
      t < sigma x ∧ ¬s.le (center t z) (s.add (s.times (physicalCount (place x t) z) s.one) target))) tailBudget) :
    s.le (s.mass L w (fun x =>
      let t := firstCut (pending x) m T
      t ∉ window N T ∨ ∃ z, ¬s.le target (s.times (physicalCount (place x t) z) s.one)))
      (s.add exitBudget (s.times ((window N T).length*(n*n)) tailBudget)) := by
  classical
  let dev (key : Nat × Cell n) (x : Ω) :=
    key.1 < sigma x ∧ ¬s.le (center key.1 key.2)
      (s.add (s.times (physicalCount (place x key.1) key.2) s.one) target)
  have bound := s.union_budget L w (rootTimes N T n) dev tailBudget (by
    intro key mem
    obtain ⟨t,ht,hkey⟩ := List.mem_flatMap.mp mem
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hkey
    exact fixed t ht z)
  rw [rootTimes_size] at bound
  apply s.trans (s.mass_mono L w (Q := fun x => exceptional x ∨
    ∃ key ∈ rootTimes N T n, dev key x) ?_)
  · exact s.trans (s.mass_or _ _ _ _) (s.mono exitBound bound)
  · intro x bad
    by_cases ex : exceptional x
    · exact .inl ex
    obtain ⟨ht,st⟩ := regular x ex
    let t := firstCut (pending x) m T
    obtain out | ⟨z,low⟩ := bad
    · exact (out ht).elim
    refine .inr ⟨(t,z),List.mem_flatMap.mpr ⟨t,ht,List.mem_map.mpr ⟨z,board_complete z,rfl⟩⟩,?_,?_⟩
    · exact Nat.lt_of_le_of_lt (window_mem.mp ht).1 st
    · intro ok
      exact low (s.cancel (s.trans (margin t ht z) ok))

end ArticuloA.Corte
#print axioms ArticuloA.Corte.random_cut_bound
