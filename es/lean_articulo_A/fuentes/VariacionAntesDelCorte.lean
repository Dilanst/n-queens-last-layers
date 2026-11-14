import SaltoDeUnSoporte
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA ArticuloA.Corte E2 E2.Regular
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def shiftAvail (a V K : α) := (V ⊗ (a ⊗ ns s 4)) ⊞ (K ⊞ ((ns s 4 ⊗ a) ⊗ V))
def pairUnit (M iz : α) := (M ⊗ cube s (ns s 2)) ⊗ quart s iz

theorem unscale (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    {v y B : α} (pos : v ≠ s.zero) (h : s.le (v ⊗ y) B) : s.le y (inv v ⊗ B) := by
  have r := s.mulMono (s.refl (inv v)) h
  rwa [←s.mulAssoc,recip _ pos,s.oneMul] at r

/-- All four coefficient budgets, in units independent of the board size. -/
theorem coeff_changes (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (n N m d : Nat) (fits : d ≤ m) (step : m+1 ≤ N) (span : N ≤ 2*n)
    (sn : ns s n ≠ s.zero) (live : ns s m ≠ s.zero) (nextPos : ns s (m+1) ≠ s.zero)
    (zeta M pi : α) (sz : zeta ≠ s.zero) (floor : s.le (ns s n ⊗ zeta) (ns s m))
    (bound : s.le (ns s n ⊗ pi) M) (p : Fin 4 → α) (hp : ∀ i, s.le (p i) s.one) (mask : Marks) :
    let size := ns s n
    let u := ratio s inv (d+1) (m+1)
    let v := ratio s inv d m
    let w := pi ⊗ cube s (ns s N)
    let old := coeff s p u (keys mask)
    let new := coeff s p v (keys mask)
    let K := pairUnit s M (inv zeta)
    let V := ns s 2 ⊗ K
    s.le new s.one ∧ s.le (feed s inv w d m ⊗ new) (inv size ⊗ V) ∧
    within s new old (inv size ⊗ (inv zeta ⊗ ns s 4)) ∧
    within s (feed s inv w d m ⊗ new) (feed s inv w (d+1) (m+1) ⊗ old)
      (inv (size ⊗ size) ⊗ shiftAvail s (inv zeta) V K) := by
  intro size u v w old new K V
  let a := inv (size ⊗ zeta)
  let k := w ⊗ quart s a
  let b := ns s N ⊗ k
  have floorLive := mul_live s inv recip sn sz
  have uu := scale_caps s inv recip n N pi zeta M sn sz span bound
  obtain ⟨aId,kk,bb⟩ := uu
  change size ⊗ a = inv zeta at aId
  change s.le ((size ⊗ size) ⊗ k) K at kk
  change s.le (size ⊗ b) V at bb
  have vLe := (step_clock s inv recip m d fits live nextPos).2.1
  have cv := (caps s p v v (keys mask) (fun i _ => hp i) (vLe ▸ up_left s _ _) (vLe ▸ up_left s _ _)).1
  have rateCap := s.mulMono (s.refl w) (quart_mono s (inv_antitone s inv recip floorLive live floor))
  have feedCap := s.mulMono (le_times s (show d ≤ N by omega) s.one) rateCap
  have bd : s.le (feed s inv w d m ⊗ new) b := by simpa only [s.mulOne] using s.mulMono feedCap cv
  obtain ⟨co,ca⟩ := (before_cut s inv recip N m d fits step live nextPos (size ⊗ zeta) w floorLive floor p hp mask).2.2
  have flip {u v c : α} (h : within s u v c) : within s v u c := ⟨h.2,h.1⟩
  refine ⟨cv,s.trans bd (unscale s inv recip sn bb),grow s (flip co) ?_,grow s (flip ca) ?_⟩
  · apply unscale s inv recip sn
    change s.le (size ⊗ (a ⊗ ns s 4)) _
    rw [←s.mulAssoc,aId]; exact s.refl _
  · apply unscale s inv recip (mul_live s inv recip sn sn)
    change s.le ((size ⊗ size) ⊗ shiftAvail s a b k) _
    have eq : (size ⊗ size) ⊗ shiftAvail s a b k =
        shiftAvail s (size ⊗ a) (size ⊗ b) ((size ⊗ size) ⊗ k) := by
      unfold shiftAvail; simp only [s.mulAdd]; ac_rfl
    rw [eq,aId]
    exact s.mono (s.mulMono bb (s.refl _)) (s.mono kk (s.mulMono (s.refl _) bb))

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.coeff_changes
