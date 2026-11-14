import Codegrados
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

def quota {n} (x : State n) (inv : α → α) (count : Nat) :=
  s.mul (inv (s.add (s.times x.reals s.one) (s.times x.virtuals s.one))) (s.times count s.one)

noncomputable def choices {n} (x : State n) (u : ColorWeights α) (inv : α → α) :=
  mixture s (quota s x inv x.reals) (quota s x inv x.virtuals)
    (choose s (realChoices s x u) .fail inv) (choose s (virtualChoices s x u) .fail inv)

theorem kernel_is_row {n} (x : State n) (t : Nat) (u : ColorWeights α) (inv : α → α)
    (running : x.failed = false) (remain : x.reals+x.virtuals ≠ 0) :
    kernel s u inv t x = (choices s x u inv).map (fun i => (i.1,next x i.2)) := by
  classical
  simp [kernel,running,remain,choices,quota]

def realAtom {n} (x : State n) (u : ColorWeights α) (inv : α → α) (e : Cell n) :=
  s.mul (quota s x inv x.reals) (s.mul (inv (total s (realChoices s x u))) (weights s u.real (lines e)))
def virtAtom {n} (x : State n) (u : ColorWeights α) (inv : α → α) (g : Edge) :=
  s.mul (quota s x inv x.virtuals) (s.mul (inv (total s (virtualChoices s x u))) (weights s u g))

def onList {ι X} (ks : List ι) (live : ι → Bool) (w : ι → α) (tag : ι → X) : Atoms α X :=
  (ks.filter live).map (fun i => (w i,tag i))

theorem regular_row {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero) :
    choices s x u inv = onList (board n) (fun e => available x (lines e)) (realAtom s x u inv) Choice.real ++
    onList (virtualEdges (2*n-1)) (available x) (virtAtom s x u inv) Choice.virtual := by
  classical
  simp only [choices,choose,if_neg rr,if_neg vv,mixture]
  simp only [realChoices,virtualChoices,realAtom,virtAtom,onList,List.map_map]; rfl

theorem mean_append {X} (a b : Atoms α X) (v : X → Nat) :
    meanN s (a++b) v = s.add (meanN s a v) (meanN s b v) := by
  induction a with
  | nil => exact (s.zero_add _).symm
  | cons i a ih => change s.add _ (meanN s (a++b) v) = s.add (s.add _ (meanN s a v)) _
                   rw [ih,s.assoc]

theorem list_budget {ι X} (ks : List ι) (live : ι → Bool) (w : ι → α) (tag : ι → X)
    (P : X → Prop) (test : ι → Bool) (B : α)
    (cap : ∀ i ∈ ks, live i → P (tag i) → s.le (w i) B)
    (inc : ∀ i ∈ ks, P (tag i) → test i) :
    s.le (meanN s (onList ks live w tag) (fun x => indicator (P x))) (s.times (ks.countP test) B) := by
  classical
  induction ks with
  | nil => exact s.refl _
  | cons i ks ih =>
    have tail := ih (fun j hj => cap j (by simp [hj])) (fun j hj => inc j (by simp [hj]))
    have skip : s.le (s.times (ks.countP test) B) (s.times ((i::ks).countP test) B) :=
      le_times s (by rw [List.countP_cons]; split <;> omega) _
    by_cases yes : live i = true
    · change s.le (meanN s (List.map _ ((i::ks).filter live)) _) _
      rw [List.filter_cons_of_pos yes,List.map_cons]
      change s.le (s.add (s.times (indicator (P (tag i))) (w i)) (meanN s (onList ks live w tag)
        (fun x => indicator (P x)))) (s.times ((i::ks).countP test) B)
      by_cases ev : P (tag i)
      · have ok := inc i (by simp) ev
        simpa [indicator,ev,MassScale.times,List.countP_cons,ok,s.comm _ s.zero,s.zero_add] using
          (s.mono (cap i (by simp) yes ev) tail)
      · simpa [indicator,ev,MassScale.times,s.zero_add] using s.trans tail skip
    · simpa [onList,List.filter_cons,yes] using s.trans tail skip

theorem pair_mass {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (Br Bv : α) (capR : ∀ e, available x (lines e) → s.le (realAtom s x u inv e) Br)
    (capV : ∀ g ∈ virtualEdges (2*n-1), available x g → s.le (virtAtom s x u inv g) Bv)
    (v w : Vertex) (ne : v ≠ w) (P : Choice n → Prop)
    (cover : ∀ a, P a → consumeVertex a v.1 v.2 ∧ consumeVertex a w.1 w.2) :
    s.le (meanN s (choices s x u inv) (fun a => indicator (P a)))
      (s.add Br (s.times ((2*n-1)*(2*n-1)) Bv)) := by
  rw [regular_row s x u inv rr vv,mean_append]
  apply s.mono
  · have h := list_budget s (board n) _ _ Choice.real P (fun e => hitsVertex (lines e) v && hitsVertex (lines e) w)
        Br (fun e _ he _ => capR e he) (by intro e _ he; simpa [hitsVertex] using cover (.real e) he)
    have one := s.trans h (le_times s (real_pair_count v w ne) Br)
    simpa [MassScale.times,s.comm _ s.zero,s.zero_add] using one
  · have h := list_budget s (virtualEdges (2*n-1)) _ _ Choice.virtual P
        (fun g => hitsVertex g v && hitsVertex g w) Bv (fun g hg hl _ => capV g hg hl)
        (by intro g _ he; simpa [hitsVertex] using cover (.virtual g) he)
    exact s.trans h (le_times s (virtual_pair_count _ v w ne) Bv)

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.pair_mass
