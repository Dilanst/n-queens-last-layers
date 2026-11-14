import TasasColor
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
def lossKeys (occ : Bool) : List Both := if occ then targets.map Sum.inr else allSlots
def singled {n} (z e : Cell n) (m : Marks) (i : Both) (a : Choice n) :=
  let v := vertex z e (ix i)
  consumeVertex a v.1 v.2 ∧ (match i with | .inl _ => True | .inr j => m j = true ∨ isReal a)
def lossMask (m : Marks) : Both → Marks | .inl _ => m | .inr j => promote m j
def guardP {n} (occ : Bool) (x : State n) (z e : Cell n) (m : Marks) (i : Both) :=
  pattern occ x z e (lossMask m i)

private theorem true_promotion {n} (occ : Bool) (x : State n) (z e : Cell n) (m : Marks)
    (j : Fin 4) (mj : m j = true) : pattern occ x z e (promote m j) = pattern occ x z e m := by
  have eq : promote m j = m := funext (fun k => by by_cases h : k=j <;> simp [promote,h,mj])
  rw [eq]

theorem guarded_hit {n} (occ : Bool) (x : State n) (good : coherent x) (z e : Cell n)
    (m : Marks) (i : Both) (a : Choice n) (live : allowed x a) :
    (pattern occ x z e m ∧ effect z e m a i) ↔ (guardP occ x z e m i ∧ singled z e m i a) := by
  have c4 (j : Fin 4) : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  cases i with
  | inl j =>
    rcases c4 j with rfl|rfl|rfl|rfl <;> simp [guardP,lossMask,effect,eraseOwn,singled,vertex,ix,slot,family]
  | inr j =>
    have geo : vertex z e (ix (.inr j)) = (side j,key z e j) := by
      rcases c4 j with rfl|rfl|rfl|rfl <;> rfl
    cases mj : m j with
    | false => simpa [guardP,lossMask,singled,geo,mj,effect] using single_vacancy occ x good z e m j mj a live
    | true => simp [guardP,lossMask,singled,geo,mj,effect,eraseDest,true_promotion _ _ _ _ _ _ mj]

variable {α : Type} (s : ProfileScale α)
open Classical in
noncomputable def weightedSingles {n} (occ : Bool) (x : State n) (z e : Cell n) (m : Marks)
    (rate : Both → α) :=
  s.sum (lossKeys occ) (fun i => if guardP occ x z e m i then rate i else s.zero)

private theorem mean_tally {X ι} (row : Atoms α X) (L : List ι) (P : Prop) (hit : X → ι → Prop) :
    meanN s row (fun a => indicator P * deathsOn L (hit a)) =
    s.sum L (fun i => meanN s row (fun a => indicator (P ∧ hit a i))) := by
  classical
  have aux (a : X) : indicator P * deathsOn L (hit a) = L.countP (fun i => decide (P ∧ hit a i)) := by
    by_cases h : P <;> simp [indicator,deathsOn,h]
  rw [funext aux,mean_count]; apply congrArg (s.sum L); funext i
  apply mean_eq; intro a _; by_cases h : P ∧ hit a.2 i <;> simp [indicator,h]

open Classical in
theorem exact_singles {n} (occ : Bool) (x : State n) (good : coherent x) (u : ColorWeights α)
    (inv : α → α) (z e : Cell n) (m : Marks) :
    let row := choices s x u inv
    meanN s row (fun a => indicator (pattern occ x z e m)*deathsOn (lossKeys occ) (effect z e m a)) =
    weightedSingles s occ x z e m (fun i => meanN s row (fun a => indicator (singled z e m i a))) := by
  classical
  dsimp only
  rw [mean_tally]; apply congrArg (s.sum (lossKeys occ)); funext i
  split
  · rename_i g
    apply mean_eq; intro a ha
    have eq := guarded_hit occ x good z e m i a.2 (row_allowed s x u inv a ha)
    simp [indicator,eq,g]
  · rename_i g
    rw [←mean_zero s (choices s x u inv)]
    apply mean_eq; intro a ha
    have eq := guarded_hit occ x good z e m i a.2 (row_allowed s x u inv a ha)
    simp [indicator,eq,g]

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.exact_singles
