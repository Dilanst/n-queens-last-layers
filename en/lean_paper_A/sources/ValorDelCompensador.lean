import PasoHastaCorte
import TranspuestaMarcas
import ObservableTerminal
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Repair ArticuloA.Corte E2 E2.Regular
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add

open Classical in
noncomputable def signedPart {n} (x : State n) (z e : Cell n) (p : Fin 4 → α) (u b : α) (odd : Bool) :=
  s.sum SizeOn.allMarks (fun m => if parity (keys m) = odd then
    coeff s p u (keys m) ⊗ ((if occupied x z e m then s.one else s.zero) ⊞
      (if availPattern x z e m then b else s.zero)) else s.zero)

private theorem initial_bits (n h : Nat) (z e : Cell n) (m : Marks) :
    ¬occupied (initial n h) z e m ∧ (availPattern (initial n h) z e m ↔ filterG z e) := by
  have empty (L : List (Cell n)) : queens (emptyMask L) = [] := by
    induction L with | nil => rfl | cons _ _ ih => exact ih
  have mask : marked (initial n h) z e m := by
    intro j; cases eq : m j <;> simp [eq,vacant,initial,empty]
  exact ⟨by simp [occupied,initial,empty],⟨fun a => a.1,fun g => ⟨g,by simp [E2.available,initial],mask⟩⟩⟩

open Classical in
theorem initial_parts (n h : Nat) (z e : Cell n) (p : Fin 4 → α) (u b : α) (odd : Bool) :
    signedPart s (initial n h) z e p u b odd =
      part s p u odd (subsets (List.finRange 4)) ⊗ (if filterG z e then b else s.zero) := by
  classical
  unfold signedPart part
  rw [←Cart.sum_scale,←four_positions,Cart.sum_map]
  apply congrArg (s.sum _); funext m
  have obs := initial_bits n h z e m
  rw [if_neg obs.1]; simp only [obs.2,s.zero_add]
  have zero (v : α) : s.zero ⊗ v = s.zero := by rw [s.mulComm,s.mulZero]
  by_cases h : parity (keys m) = odd <;> simp [h,zero]

open Classical in
theorem initial_value (n h : Nat) (z e : Cell n) (p vacancy : Fin 4 → α) (y b : α)
    (factors : ∀ i, vacancy i ⊞ (y ⊗ p i) = s.one) :
    signedPart s (initial n h) z e p y b false =
      ((if filterG z e then b else s.zero) ⊗ s.four vacancy) ⊞ signedPart s (initial n h) z e p y b true := by
  rw [initial_parts,initial_parts,initial_product s p vacancy y _ (fun i _ => factors i),s.addMul]
  have eq : prodLines s vacancy (List.finRange 4) = s.four vacancy := by
    rw [show List.finRange 4 = [0,1,2,3] by decide]
    simp only [prodLines,ProfileScale.four,s.mulOne,s.mulAssoc]
  rw [eq,s.mulComm (s.four vacancy)]

private theorem sum_filter {ι} (L : List ι) (f : ι → α) (ok : ι → Bool) :
    s.sum L (fun i => if ok i then f i else s.zero) = s.sum (L.filter ok) f := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    cases h : ok i <;> simp [MassScale.sum,List.filter_cons,h,s.zero_add] at ih ⊢ <;> rw [ih]

open Classical in
theorem terminal_value {n} (x : State n) (z e : Cell n) (p : Fin 4 → α) (odd : Bool) :
    signedPart s x z e p s.zero s.zero odd =
      if odd = false ∧ Candidate x.physical z e then s.one else s.zero := by
  classical
  let f := fun m : Marks => if parity (keys m)=odd ∧ occupied x z e m then s.one else s.zero
  have emptyMaskList : SizeOn.allMarks.filter (fun m => (keys m).isEmpty) =
      [SizeOn.maskOf false false false false] := by rfl
  have unmarked : SizeOn.maskOf false false false false = fun _ => false := by
    funext j; have c : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases c with rfl|rfl|rfl|rfl <;> rfl
  unfold signedPart
  have zero (v : α) : s.zero ⊗ v = s.zero := by rw [s.mulComm,s.mulZero]
  have right (v : α) : v ⊞ s.zero = v := by rw [s.comm,s.zero_add]
  calc
    _ = s.sum SizeOn.allMarks (fun m => if (keys m).isEmpty then f m else s.zero) := by
      apply congrArg (s.sum _); funext m
      rw [terminal_magnitude]
      cases h : (keys m).isEmpty <;> by_cases a : occupied x z e m <;> by_cases t : parity (keys m)=odd <;>
        simp [h,a,t,f,s.oneMul,zero,s.mulZero,s.zero_add,right]
    _ = _ := by
      rw [sum_filter,emptyMaskList,unmarked]
      have em : keys (fun _ => false) = [] := by decide
      simp [MassScale.sum,f,em,parity,unmarked_eq_candidate,s.comm _ s.zero,s.zero_add,eq_comm]

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.initial_value
#print axioms ArticuloA.Trayectoria.Adjunto.terminal_value
