import VariacionAntesDelCorte
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Repair ArticuloA.Corte E2 E2.Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

noncomputable def rootPart {n} (inv : α → α) (N m d : Nat) (z : Cell n)
    (p : Cell n → Fin 4 → α) (pi : Cell n → α) (x : State n) (j : Bool) :=
  s.sum (board n) (fun e => signedPart s x z e (p e) (ratio s inv d m)
    (feed s inv (pi e ⊗ cube s (ns s N)) d m) j)

def oneMaskCap (iz M : α) :=
  let K := pairUnit s M iz
  let V := ns s 2 ⊗ K
  (ns s 5 ⊞ (iz ⊗ ns s 4)) ⊞ (s.times 8 V ⊞ shiftAvail s iz V K)

theorem kernel_jump {n} (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (w : ColorWeights α) (t N m d : Nat) (fits : d ≤ m) (step : m+1 ≤ N) (span : N ≤ 2*n)
    (sn : ns s n ≠ s.zero) (live : ns s m ≠ s.zero) (nextPos : ns s (m+1) ≠ s.zero)
    (zeta M : α) (sz : zeta ≠ s.zero) (floor : s.le (ns s n ⊗ zeta) (ns s m))
    (z : Cell n) (p : Cell n → Fin 4 → α) (pi : Cell n → α)
    (bound : ∀ e, s.le (ns s n ⊗ pi e) M) (hp : ∀ e i, s.le (p e i) s.one)
    (x : State n) (good : coherent x) (i : α × State n) (hi : i ∈ kernel s w inv t x) :
    let f := rootPart s inv N m d z p pi i.2
    let o := rootPart s inv N (m+1) (d+1) z p pi x
    within s (f false ⊞ o true) (f true ⊞ o false) (s.times 16 (oneMaskCap s (inv zeta) M)) := by
  intro f o
  let y := i.2
  let size := ns s n
  let K := pairUnit s M (inv zeta)
  let V := ns s 2 ⊗ K
  let G := inv zeta ⊗ ns s 4
  let D := shiftAvail s (inv zeta) V K
  let u := ratio s inv (d+1) (m+1)
  let v := ratio s inv d m
  let weight := fun e => pi e ⊗ cube s (ns s N)
  let C := fun v (l : Marks) (e : Cell n) => coeff s (p e) v (keys l)
  let part := fun (x : State n) v (b : Cell n → α) l =>
    gated s (board n) (occBit x z l) (C v l) ⊞ gated s (board n) (avBit x z l) (fun e => b e ⊗ C v l e)
  let before := part x u (fun e => feed s inv (weight e) (d+1) (m+1))
  let after := part y v (fun e => feed s inv (weight e) d m)
  have counts (l : Marks) := step_supports x good.1 z l .fail (by trivial)
  have moves (l : Marks) :
      (board n).countP (fun e => occBit x z l e != occBit y z l e) ≤ 5 ∧
      (board n).countP (fun e => avBit x z l e != avBit y z l e) ≤ 8*n := by
    rcases kernel_child s w inv t x i hi with eq | ⟨move,ok,eq⟩
    · change _ ∧ _; dsimp only [y]; rw [eq]
      simpa only [bne_self_eq_false,List.countP_false] using
        (show 0 ≤ 5 ∧ 0 ≤ 8*n by omega)
    · dsimp only [y]; rw [eq]
      have h := step_supports x good.1 z l move (choice_adm good move ok)
      exact ⟨h.1,h.2.1⟩
  have cut := fun e l => coeff_changes s inv recip n N m d fits step span sn live nextPos zeta M
    (pi e) sz floor (bound e) (p e) (hp e) l
  have reduce (j : Nat) (sj : ns s j ≠ s.zero) (a : α) : s.times j (inv (ns s j) ⊗ a) = a := by
    rw [times_m,←s.mulAssoc,s.mulComm (ns s j) _,recip _ sj,s.oneMul]
  have nn : ns s (n*n) ≠ s.zero := by rw [size_mult]; exact mul_live s inv recip sn sn
  have each (l : Marks) : within s (after l) (before l) (oneMaskCap s (inv zeta) M) := by
    have hO := support_jump s (board n) (occBit x z l) (occBit y z l) (C u l) (C v l)
      s.one (inv size ⊗ G) (fun e => (cut e l).1) (fun e => (cut e l).2.2.1)
    have hD := support_jump s (board n) (avBit x z l) (avBit y z l)
      (fun e => feed s inv (weight e) (d+1) (m+1) ⊗ C u l e)
      (fun e => feed s inv (weight e) d m ⊗ C v l e) (inv size ⊗ V)
      (inv (size ⊗ size) ⊗ D) (fun e => (cut e l).2.1) (fun e => (cut e l).2.2.2)
    apply grow s (within_add s hO hD)
    have h := s.mono (s.mono (le_times s (moves l).1 s.one) (le_times s (counts l).2.2.1 (inv size ⊗ G)))
      (s.mono (le_times s (moves l).2 (inv size ⊗ V)) (le_times s (counts l).2.2.2 (inv (size ⊗ size) ⊗ D)))
    have collapse : s.times (8*n) (inv size ⊗ V) = s.times 8 V := by
      dsimp only [size]; rw [times_m,size_mult,s.mulAssoc,←times_m s n,reduce n sn,times_m]
    dsimp only [size] at h collapse
    have reduce2 := reduce (n*n) nn D
    rw [size_mult] at reduce2
    rw [reduce n sn,collapse,reduce2] at h
    exact h
  have group (j : Bool) : within s (f j) (o j) (s.times (masks j).length (oneMaskCap s (inv zeta) M)) := by
    dsimp only [f,o,rootPart]; rw [by_mask,by_mask,←const_sum]
    exact balance_sum s (masks j) after before _ each
  have both := within_add s (group false) (show within s (o true) (f true) _ from ⟨(group true).2,(group true).1⟩)
  rw [s.comm (o false) (f true),←plus_times] at both
  exact both

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.kernel_jump
