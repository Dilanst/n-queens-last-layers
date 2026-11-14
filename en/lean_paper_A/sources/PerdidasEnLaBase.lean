import CanalesDeParidad
import DerivaEnRegion
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte ArticuloA.Repair E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.add := ⟨s.assoc⟩
local instance : Std.Commutative s.add := ⟨s.comm⟩
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

open Classical in
noncomputable def bit {n} (o : Bool) (x : State n) (z e : Cell n) (m : Marks) :=
  if pattern o x z e m then s.one else s.zero

def selfRate (o : Bool) (a : α) (m : Marks) :=
  if o then ns s (keys m).length ⊗ a else s.times 4 a ⊞ (ns s (keys m).length ⊗ a)

theorem partition_sum {ι} (L : List ι) (m : ι → Bool) (f : ι → α) :
    s.sum L f = s.sum (L.filter m) f ⊞ s.sum (L.filter (fun i => !(m i))) f := by
  induction L with
  | nil => exact (s.zero_add _).symm
  | cons i L ih =>
    cases h : m i <;> simp only [List.filter_cons,h,Bool.not_false,Bool.not_true,if_true,
      Bool.false_eq_true,if_false] <;>
      simp only [MassScale.sum,List.foldr_cons] at ih ⊢ <;> rw [ih] <;> ac_rfl

theorem const_sum {ι} (L : List ι) (v : α) : s.sum L (fun _ => v) = s.times L.length v := by
  induction L with | nil => rfl | cons i L ih => exact congrArg (s.add v) ih

theorem left_sum {ι} (L : List ι) (f : ι → α) (a : α) :
    s.sum L (fun i => a ⊗ f i) = a ⊗ s.sum L f := by
  conv => lhs; arg 3; ext i; rw [s.mulComm]
  rw [Cart.sum_scale,s.mulComm]

open Classical in
theorem losses_in_basis {n} (o : Bool) (x : State n) (z e : Cell n) (m : Marks)
    (a : α) (p : Fin 4 → α) :
    weightedSingles s o x z e m (referenceRate a (fun i => a ⊗ p i) m) =
      (selfRate s o a m ⊗ bit s o x z e m) ⊞ (a ⊗ cross s p (bit s o x z e) m) := by
  classical
  let Z := bit s o x z e
  let f := fun i => if guardP o x z e m (.inr i) then referenceRate a (fun i => a ⊗ p i) m (.inr i) else s.zero
  have gate (v : α) (j : Marks) : (if pattern o x z e j then v else s.zero) = v ⊗ Z j := by
    by_cases h : pattern o x z e j <;> simp [Z,bit,h,s.mulZero,s.mulOne]
  have marked : s.sum (keys m) f = (ns s (keys m).length ⊗ a) ⊗ Z m := by
    calc
      _ = s.sum (keys m) (fun _ => a ⊗ Z m) := by
        apply sum_agree
        intro i hi; have mi := (List.mem_filter.mp hi).2
        have eq : promote m i = m := funext (fun j => by by_cases h : j=i <;> simp [promote,h,mi])
        simpa [f,guardP,lossMask,referenceRate,mi,eq] using gate a m
      _ = _ := by rw [const_sum,times_m,s.mulAssoc]
  have unmarked : s.sum (upper m) f = a ⊗ cross s p Z m := by
    unfold cross; rw [←left_sum]
    apply sum_agree; intro i hi
    have mi : m i = false := by simpa using (List.mem_filter.mp hi).2
    simpa [f,guardP,lossMask,referenceRate,mi,s.mulAssoc] using gate (a ⊗ p i) (promote m i)
  have dest : s.sum targets f = ((ns s (keys m).length ⊗ a) ⊗ Z m) ⊞ (a ⊗ cross s p Z m) :=
    (partition_sum s targets m f).trans (by change s.sum (keys m) f ⊞ s.sum (upper m) f = _; rw [marked,unmarked])
  have own : s.sum targets (fun i => if guardP o x z e m (.inl i) then a else s.zero) = s.times 4 a ⊗ Z m := by
    change s.sum targets (fun _ => if pattern o x z e m then a else s.zero) = _
    rw [gate,const_sum,times_m,times_m,s.mulAssoc]; rfl
  unfold weightedSingles
  cases o
  · simp only [lossKeys,allSlots,Bool.false_eq_true,if_false,Cart.sum_cat,Cart.sum_map]
    change s.sum targets (fun i => if guardP false x z e m (.inl i) then a else s.zero) ⊞ s.sum targets f = _
    rw [own,dest]; simp only [selfRate,Bool.false_eq_true,if_false,s.addMul,Z,s.assoc]
  · exact (Cart.sum_map s targets Sum.inr _).trans dest
  where
    sum_agree {ι : Type} {L : List ι} {f g : ι → α} (h : ∀ i ∈ L, f i = g i) : s.sum L f = s.sum L g := by
      induction L with
      | nil => rfl
      | cons i L ih => change f i ⊞ s.sum L f = g i ⊞ s.sum L g; rw [h i (by simp),ih (fun j hj => h j (by simp [hj]))]

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.losses_in_basis
