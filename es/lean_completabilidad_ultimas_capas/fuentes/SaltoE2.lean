import SoportesPaso

namespace ArticuloA.Trayectoria
open ArticuloA ArticuloA.Repair ArticuloA.Corte E2
namespace SizeOn
variable {α β : Type} {s : MassScale β} (g : SizeOn α β s)

private theorem rep_add (i j : Nat) (v : β) :
    repeatMass (s:=s) (i+j) v = s.add (repeatMass (s:=s) i v) (repeatMass (s:=s) j v) := by
  induction i with
  | zero => simp [repeatMass,s.zero_add]
  | succ i ih => rw [Nat.succ_add]; change s.add v _ = s.add (s.add v _) _; rw [ih,s.assoc]

private theorem rep_mul (i j : Nat) (v : β) :
    repeatMass (s:=s) (i*j) v = repeatMass (s:=s) i (repeatMass (s:=s) j v) := by
  induction i with
  | zero => simp [repeatMass]
  | succ i ih => rw [Nat.succ_mul,rep_add,ih,s.comm]; rfl

private theorem rep_level {i j : Nat} (h : i ≤ j) (v : β) :
    s.le (repeatMass (s:=s) i v) (repeatMass (s:=s) j v) := by
  obtain ⟨d,rfl⟩ := Nat.le.dest h
  rw [rep_add]; have b := s.mono (s.refl (repeatMass (s:=s) i v)) (s.zero_le (repeatMass (s:=s) d v))
  simpa [s.comm _ s.zero,s.zero_add] using b

private theorem rep_weight (i : Nat) {v w : β} (h : s.le v w) :
    s.le (repeatMass (s:=s) i v) (repeatMass (s:=s) i w) := by
  induction i with
  | zero => exact s.refl _
  | succ _ ih => exact s.mono h ih

noncomputable def component {n} (x : State n) (z : Cell n) (m : Marks) (co ca : Cell n → α) :=
  g.add (g.score (board n) (occBit x z m) co) (g.score (board n) (avBit x z m) ca)

/-- Four scalar bounds: C on occupied coefficients, C/n on their variations,
C/n on available coefficients and C/n² on their variations, without division. -/
theorem component_jump {n} (x : State n) (ok : Legal x.physical) (z : Cell n)
    (m : Marks) (move : Choice n) (adm : admissible x move)
    (co ca co' ca' : Cell n → α) (C Do Ja Da : β)
    (occ : ∀ e, s.le (g.dist (co' e) g.zero) C)
    (dOcc : ∀ e, s.le (g.dist (co e) (co' e)) Do)
    (av : ∀ e, s.le (g.dist (ca' e) g.zero) Ja)
    (dAv : ∀ e, s.le (g.dist (ca e) (ca' e)) Da)
    (caps : s.le (repeatMass (s:=s) n Do) C ∧ s.le (repeatMass (s:=s) n Ja) C ∧ s.le (repeatMass (s:=s) (n*n) Da) C) :
    s.le (g.dist (g.component x z m co ca) (g.component (next x move) z m co' ca'))
      (repeatMass (s:=s) 15 C) := by
  obtain ⟨h1,h2,h3,h4⟩ := step_supports x ok z m move adm
  have oc := g.block_jump (board n) (occBit x z m) (occBit (next x move) z m) co co' C Do
    (fun e _ _ => occ e) (fun e _ _ => dOcc e)
  have ac := g.block_jump (board n) (avBit x z m) (avBit (next x move) z m) ca ca' Ja Da
    (fun e _ _ => av e) (fun e _ _ => dAv e)
  rw [budget_counts] at oc ac
  have one : repeatMass (s:=s) 1 C = C := by change s.add C s.zero = C; rw [s.comm,s.zero_add]
  have left := s.trans oc (s.mono (rep_level h1 C) (s.trans (rep_level h3 Do) caps.1))
  have acht := rep_level (s:=s) h2 Ja
  rw [rep_mul] at acht
  have right := s.trans ac (s.mono (s.trans acht (rep_weight 8 caps.2.1))
    (s.trans (rep_level h4 Da) caps.2.2))
  have tot := s.trans (g.addBound _ _ _ _) (s.mono left right)
  have add : repeatMass (s:=s) 15 C = s.add (s.add (repeatMass (s:=s) 5 C) C) (s.add (repeatMass (s:=s) 8 C) C) := by
    calc
      _ = s.add (repeatMass (s:=s) 6 C) (repeatMass (s:=s) 9 C) := rep_add 6 9 C
      _ = _ := by rw [rep_add 5 1 C,rep_add 8 1 C,one]
  rwa [add]

/-- Sum over the sixteen subsets J. Each summand includes both occupied and
available patterns. Coefficients are allowed to vary by cell and by J. -/
theorem sum_components (ms : List Marks) (old new : Marks → α) (C : β)
    (each : ∀ m ∈ ms, s.le (g.dist (old m) (new m)) (repeatMass (s:=s) 15 C)) :
    s.le (g.dist (ms.foldr (fun m v => g.add (old m) v) g.zero)
      (ms.foldr (fun m v => g.add (new m) v) g.zero)) (repeatMass (s:=s) (ms.length*15) C) := by
  induction ms with
  | nil => change s.le (g.dist g.zero g.zero) s.zero; rw [g.self]; exact s.refl _
  | cons m ms ih =>
    rw [List.length_cons,Nat.succ_mul,Nat.add_comm,rep_add]
    exact s.trans (g.addBound _ _ _ _) (s.mono (each m (by simp)) (ih (fun m hm => each m (by simp [hm]))))

def maskOf (a b c d : Bool) : Marks
  | 0 => a | 1 => b | 2 => c | 3 => d
def allMarks : List Marks :=
  let bits := [false,true]
  bits.flatMap fun a => bits.flatMap fun b => bits.flatMap fun c => bits.map fun d => maskOf a b c d

theorem all_marks_cover (m : Marks) : m ∈ allMarks := by
  have eq : maskOf (m 0) (m 1) (m 2) (m 3) = m := by
    funext j; have h : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases h with rfl|rfl|rfl|rfl <;> rfl
  have mem (b : Bool) : b ∈ [false,true] := by cases b <;> simp
  exact List.mem_flatMap.mpr ⟨_,mem (m 0),List.mem_flatMap.mpr ⟨_,mem (m 1),
    List.mem_flatMap.mpr ⟨_,mem (m 2),List.mem_map.mpr ⟨_,mem (m 3),eq⟩⟩⟩⟩

noncomputable def phi {n} (x : State n) (z : Cell n) (co ca : Marks → Cell n → α) :=
  allMarks.foldr (fun m v => g.add (g.component x z m (co m) (ca m)) v) g.zero

theorem phi_jump {n} (x : State n) (ok : Legal x.physical) (z : Cell n)
    (move : Choice n) (adm : admissible x move) (co ca co' ca' : Marks → Cell n → α)
    (C Do Ja Da : β) (occ : ∀ m e, s.le (g.dist (co' m e) g.zero) C)
    (dOcc : ∀ m e, s.le (g.dist (co m e) (co' m e)) Do)
    (av : ∀ m e, s.le (g.dist (ca' m e) g.zero) Ja)
    (dAv : ∀ m e, s.le (g.dist (ca m e) (ca' m e)) Da)
    (caps : s.le (repeatMass (s:=s) n Do) C ∧ s.le (repeatMass (s:=s) n Ja) C ∧
      s.le (repeatMass (s:=s) (n*n) Da) C) :
    s.le (g.dist (g.phi x z co ca) (g.phi (next x move) z co' ca')) (repeatMass (s:=s) 240 C) := by
  exact g.sum_components allMarks _ _ C (fun m _ =>
    g.component_jump x ok z m move adm _ _ _ _ C Do Ja Da (occ m) (dOcc m) (av m) (dAv m) caps)

end SizeOn
end ArticuloA.Trayectoria
#print axioms ArticuloA.Trayectoria.SizeOn.component_jump
#print axioms ArticuloA.Trayectoria.SizeOn.sum_components
#print axioms ArticuloA.Trayectoria.SizeOn.phi_jump
