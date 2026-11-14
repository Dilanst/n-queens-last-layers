import SaltoE2

namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel

def coherent {n} (x : State n) : Prop := Legal x.physical ∧
  ∀ e ∈ queens x.physical, ∀ i, x.active i (lines e i) = false
def allowed {n} (x : State n) : Choice n → Prop
  | .real c => available x (lines c) = true
  | .virtual e => available x e = true
  | .fail => True

theorem initial_coherent (n h : Nat) : coherent (initial n h) := by
  have empty (xs : List (Cell n)) : queens (emptyMask xs) = [] := by
    induction xs with | nil => rfl | cons _ _ ih => exact ih
  simp [coherent,initial,Legal,empty]

private theorem active_on {n} {x : State n} {v : Edge} (live : available x v = true) (i : Fin 4) :
    x.active i (v i) = true := List.all_eq_true.mp live i (by simp [List.finRange,List.mem_ofFn] <;> omega)

theorem choice_adm {n} {x : State n} (good : coherent x) (a : Choice n) (ok : allowed x a) :
    admissible x a := by
  cases a with
  | real c => intro old; have h := good.2 c old 0; have l := active_on ok 0; simp_all
  | virtual _ => trivial
  | fail => trivial

private theorem new_compatible {n} {x : State n} (good : coherent x) {c e : Cell n}
    (ok : available x (lines c) = true) (old : e ∈ queens x.physical) : compatible c e := by
  have diff (i : Fin 4) : lines c i ≠ lines e i := by
    intro eq; have v := active_on ok i; rw [eq,good.2 e old i] at v; contradiction
  have h0 := diff 0; have h1 := diff 1; have h2 := diff 2; have h3 := diff 3
  simp [lines] at h0 h1 h2 h3
  exact ⟨fun h => h0 (congrArg Fin.val h),fun h => h1 (congrArg Fin.val h),by omega,h3⟩

theorem next_coherent {n} {x : State n} (good : coherent x) (a : Choice n) (ok : allowed x a) :
    coherent (next x a) := by
  cases a with
  | fail => exact good
  | virtual e =>
    exact ⟨good.1,fun c old i => by simp [next,consume,good.2 c old i]⟩
  | real c =>
    have fresh := choice_adm good (.real c) ok
    have splitOld := inserted x.physical c fresh
    have sub {xs} (b : @Mask (Cell n) xs) : (queens b).Sublist xs := by
      induction b with | empty => exact .slnil | skip _ ih => exact .cons _ ih | take _ ih => exact .cons₂ _ ih
    constructor
    · have nd := List.Pairwise.sublist (sub (toggle c x.physical)) (board_unique n)
      apply nd.imp_of_mem
      intro e f oldE oldF ne
      rcases (splitOld e).mp oldE with rfl|he <;> rcases (splitOld f).mp oldF with rfl|hf
      · exact (ne rfl).elim
      · exact new_compatible good ok hf
      · have h := new_compatible good ok he
        exact ⟨Ne.symm h.1,Ne.symm h.2.1,Ne.symm h.2.2.1,Ne.symm h.2.2.2⟩
      · exact legal_pair good.1 he hf ne
    · intro e old i; rcases (splitOld e).mp old with rfl|he
      · simp [next,consume]
      · simp [next,consume,good.2 e he i]

variable {α : Type} (s : ProfileScale α)
private theorem choose_support {X} (edges : Atoms α X) (fail : X) (inv : α → α)
    (i : α × X) (member : i ∈ choose s edges fail inv) : i.2 = fail ∨ ∃ j ∈ edges, i.2 = j.2 := by
  classical
  unfold choose at member; split at member
  · have eq := List.mem_singleton.mp member; exact .inl (congrArg Prod.snd eq)
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp member; exact .inr ⟨j,hj,rfl⟩

theorem kernel_child {n} (u : ColorWeights α) (inv : α → α) (t : Nat) (x : State n)
    (i : α × State n) (hi : i ∈ kernel s u inv t x) :
    i.2 = x ∨ ∃ a, allowed x a ∧ i.2 = next x a := by
  classical
  unfold kernel at hi; split at hi
  · exact .inl (congrArg Prod.snd (List.mem_singleton.mp hi))
  right; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  rcases List.mem_append.mp hj with hr|hv
  · obtain ⟨v,mem,rfl⟩ := List.mem_map.mp hr
    rcases choose_support s _ _ _ _ mem with fail | ⟨e,he,eq⟩
    · exact ⟨.fail,trivial,congrArg (next x) fail⟩
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
      exact ⟨.real c,(List.mem_filter.mp hc).2,congrArg (next x) eq⟩
  · obtain ⟨v,mem,rfl⟩ := List.mem_map.mp hv
    rcases choose_support s _ _ _ _ mem with fail | ⟨e,he,eq⟩
    · exact ⟨.fail,trivial,congrArg (next x) fail⟩
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
      exact ⟨.virtual v,(List.mem_filter.mp hv).2,congrArg (next x) eq⟩

theorem all_leaves_coherent {n} (u : ColorWeights α) (inv : α → α) (t m : Nat)
    (x : State n) (good : coherent x) (i : α × State n) (hi : i ∈ leaves s (kernel s u inv) t m x) :
    coherent i.2 := by
  induction m generalizing t x i with
  | zero => exact (congrArg Prod.snd (List.mem_singleton.mp hi)) ▸ good
  | succ m ih =>
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
    apply ih (t+1) a.2 _ j hj
    rcases kernel_child s u inv t x a ha with same | ⟨move,ok,eq⟩
    · rw [same]; exact good
    · rw [eq]; exact next_coherent good move ok

/-- The bound now ranges over every outcome in the E2 row, including a failure
or an irregular arriving state. Arrival-coefficient bounds must hold there. -/
theorem kernel_phi_jump {n β V} {b : MassScale β} (g : SizeOn V β b)
    (u : ColorWeights α) (inv : α → α) (t : Nat) (x : State n) (good : coherent x)
    (i : α × State n) (hi : i ∈ kernel s u inv t x) (z : Cell n)
    (co ca co' ca' : Marks → Cell n → V) (C Do Ja Da : β)
    (occ : ∀ m e, b.le (g.dist (co' m e) g.zero) C)
    (dOcc : ∀ m e, b.le (g.dist (co m e) (co' m e)) Do)
    (av : ∀ m e, b.le (g.dist (ca' m e) g.zero) Ja)
    (dAv : ∀ m e, b.le (g.dist (ca m e) (ca' m e)) Da)
    (caps : b.le (SizeOn.repeatMass (s:=b) n Do) C ∧ b.le (SizeOn.repeatMass (s:=b) n Ja) C ∧
      b.le (SizeOn.repeatMass (s:=b) (n*n) Da) C) :
    b.le (g.dist (g.phi x z co ca) (g.phi i.2 z co' ca')) (SizeOn.repeatMass (s:=b) 240 C) := by
  rcases kernel_child s u inv t x i hi with eq | ⟨a,ad,eq⟩
  · rw [eq]; exact g.phi_jump x good.1 z .fail trivial _ _ _ _ _ _ _ _ occ dOcc av dAv caps
  · rw [eq]; exact g.phi_jump x good.1 z a (choice_adm good a ad) _ _ _ _ _ _ _ _ occ dOcc av dAv caps

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.all_leaves_coherent
#print axioms ArticuloA.Trayectoria.E2.kernel_phi_jump
