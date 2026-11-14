import DerivaPatrones
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
namespace Cart
variable {α : Type} (s : ProfileScale α)

theorem sum_scale {ι} (L : List ι) (v : ι → α) (a : α) :
    s.sum L (fun i => s.mul (v i) a) = s.mul (s.sum L v) a := by
  induction L with
  | nil => change s.zero = s.mul s.zero a; rw [s.mulComm,s.mulZero]
  | cons i L ih => change s.add (s.mul (v i) a) (s.sum L _) = s.mul (s.add (v i) (s.sum L v)) a
                   rw [ih,s.addMul]

theorem sum_map {ι X} (L : List ι) (tag : ι → X) (f : X → α) :
    s.sum (L.map tag) f = s.sum L (fun i => f (tag i)) := by
  induction L with | nil => rfl | cons i L ih => change s.add _ (s.sum (L.map tag) f) = s.add _ (s.sum L _); rw [ih]

theorem sum_cat {ι} (L M : List ι) (f : ι → α) : s.sum (L++M) f = s.add (s.sum L f) (s.sum M f) := by
  induction L with | nil => exact (s.zero_add _).symm
                   | cons i L ih => change s.add _ (s.sum (L++M) f) = s.add (s.add _ (s.sum L f)) _
                                    rw [ih,s.assoc]

theorem sum_flat {ι X} (L : List ι) (g : ι → List X) (f : X → α) :
    s.sum (L.flatMap g) f = s.sum L (fun i => s.sum (g i) f) := by
  induction L with | nil => rfl
                   | cons i L ih => change s.sum (g i ++ L.flatMap g) f = s.add _ (s.sum L _); rw [sum_cat,ih]

private theorem pull {ι} (L : List ι) (a : α) (f : ι → α) :
    s.sum L (fun i => s.mul a (f i)) = s.mul a (s.sum L f) := by
  conv => lhs; arg 3; ext i; rw [s.mulComm]
  rw [sum_scale,s.mulComm]

theorem full (N : Nat) (u : Fin 4 → Nat → α) :
    s.sum (virtualEdges N) (weights s u) = s.four (fun i => s.sum (List.range N) (u i)) := by
  unfold virtualEdges weights ProfileScale.four
  simp only [sum_flat,sum_map]
  let r := List.range N
  simp only [← s.mulAssoc]
  have inner (i j d : Nat) := pull s r (s.mul (s.mul (u 0 i) (u 1 j)) (u 2 d)) (u 3)
  change s.sum r (fun i => s.sum r (fun j => s.sum r (fun d => s.sum r (fun a =>
    s.mul (s.mul (s.mul (u 0 i) (u 1 j)) (u 2 d)) (u 3 a))))) = _
  simp only [inner]
  have onD (i j : Nat) := sum_scale s r (fun d => s.mul (s.mul (u 0 i) (u 1 j)) (u 2 d)) (s.sum r (u 3))
  have getD (i j : Nat) := pull s r (s.mul (u 0 i) (u 1 j)) (u 2)
  simp only [onD,getD]
  have onJ (i : Nat) := sum_scale s r (fun j => s.mul (s.mul (u 0 i) (u 1 j)) (s.sum r (u 2))) (s.sum r (u 3))
  have onJ' (i : Nat) := sum_scale s r (fun j => s.mul (u 0 i) (u 1 j)) (s.sum r (u 2))
  have getJ (i : Nat) := pull s r (u 0 i) (u 1)
  simp only [onJ,onJ',getJ]
  rw [sum_scale s r (fun i => s.mul (s.mul (u 0 i) (s.sum r (u 1))) (s.sum r (u 2))),
    sum_scale s r (fun i => s.mul (u 0 i) (s.sum r (u 1))),sum_scale s r (u 0)]

theorem weight_gate (u : Fin 4 → Nat → α) (f : Fin 4 → Nat → Bool) (g : Edge) :
    weights s (fun i v => if f i v then u i v else s.zero) g =
      if at4 f g then weights s u g else s.zero := by
  have zeroL (a : α) : s.mul s.zero a = s.zero := by rw [s.mulComm,s.mulZero]
  cases h0 : f 0 (g 0) <;> cases h1 : f 1 (g 1) <;> cases h2 : f 2 (g 2) <;>
    cases h3 : f 3 (g 3) <;> simp [weights,at4,ProfileScale.four,h0,h1,h2,h3,zeroL,s.mulZero]

theorem truncated (N : Nat) (u : Fin 4 → Nat → α) (f : Fin 4 → Nat → Bool) :
    s.sum (virtualEdges N) (fun g => if at4 f g then weights s u g else s.zero) =
    s.four (fun i => s.sum (List.range N) (fun v => if f i v then u i v else s.zero)) := by
  rw [← full]; exact congrArg (s.sum (virtualEdges N)) (funext (fun g => (weight_gate s u f g).symm))

theorem active_eq {n} (x : State n) (g : Edge) : available x g = at4 x.active g := by
  simp [available,at4,List.finRange,List.ofFn_succ,Bool.and_assoc]

theorem total_list {ι X} (L : List ι) (f : ι → Bool) (w : ι → α) (tag : ι → X) :
    total s (onList L f w tag) = s.sum L (fun i => if f i then w i else s.zero) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    cases h : f i <;> simp [onList,ProfileKernel.total,avg,MassScale.sum,List.filter_cons,h,s.mulOne,s.zero_add] at ih ⊢
    all_goals rw [ih]

def part {n} (x : State n) (u : Fin 4 → Nat → α) (i : Fin 4) :=
  s.sum (List.range (2*n-1)) (fun v => if x.active i v then u i v else s.zero)

theorem normalizer {n} (x : State n) (u : Fin 4 → Nat → α) :
    total s (virtualChoices s x u) = s.four (part s x u) := by
  change total s (onList _ _ _ _) = _
  rw [total_list]; simp only [active_eq]; exact truncated s _ u x.active

end Cart
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.Cart.normalizer
