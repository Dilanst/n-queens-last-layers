import ExtremosAdjunto
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2.Regular Control
variable {α : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩

def occupiedCap (a : α) := (a ⊗ a) ⊗ ns s 6
def availCap (a b k : α) :=
  ((k ⊞ ((ns s 4 ⊗ a) ⊗ b)) ⊗ (a ⊗ ns s 4)) ⊞
    ((b ⊗ occupiedCap s a) ⊞ (occupiedCap s a ⊗ b))

theorem quart_mono {a b : α} (h : a ≼ b) : quart s a ≼ quart s b :=
  s.mulMono (s.mulMono h h) (s.mulMono h h)

theorem before_cut (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (N m d : Nat) (fits : d ≤ m) (step : m+1 ≤ N)
    (live : ns s m ≠ s.zero) (nextPos : ns s (m+1) ≠ s.zero)
    (floor w : α) (fl : floor ≠ s.zero) (margin : floor ≼ ns s m)
    (p : Fin 4 → α) (hp : ∀ i, p i ≼ s.one) (mask : E2.Marks) :
    let J := keys mask
    let v := ratio s inv d m
    let u := ratio s inv (d+1) (m+1)
    let a := inv (ns s (m+1))
    let k := rate s inv w (m+1)
    let old := feed s inv w (d+1) (m+1)
    let new := feed s inv w d m
    let A := inv floor
    let K := w ⊗ quart s A
    let B := ns s N ⊗ K
    let C := coeff s p v J
    let row := ns s J.length ⊗ a
    let pred := a ⊗ predecessor s (coeff s p v) p J
    within s (coeff s p u J ⊞ (row ⊗ C)) (C ⊞ pred) (occupiedCap s A) ∧
    within s ((old ⊗ coeff s p u J) ⊞ (((s.times 4 a ⊞ row) ⊗ new) ⊗ C))
      (((new ⊗ C) ⊞ (new ⊗ pred)) ⊞ (k ⊗ C)) (availCap s A B K) ∧
    within s (coeff s p u J) C (A ⊗ ns s 4) ∧
    within s (old ⊗ coeff s p u J) (new ⊗ C) ((B ⊗ (A ⊗ ns s 4)) ⊞ (K ⊞ ((ns s 4 ⊗ A) ⊗ B))) := by
  intro J v u a k old new A K B C row pred
  obtain ⟨hr,hv,hu⟩ := step_clock s inv recip m d fits live nextPos
  have l' := s.trans margin (le_times s (Nat.le_succ m) s.one)
  have ac := inv_antitone s inv recip fl nextPos l'
  have kc := s.mulMono (s.refl w) (quart_mono s ac)
  have kn := s.mulMono (s.refl w) (quart_mono s (inv_antitone s inv recip fl live margin))
  have bc := s.mulMono (le_times s (show d+1 ≤ N by omega) s.one) kc
  have bn := s.mulMono (le_times s (show d ≤ N by omega) s.one) kn
  have ucap := s.mulMono (s.refl (inv (ns s (m+1)))) (le_times s (Nat.succ_le_succ fits) s.one)
  change s.le u (inv (ns s (m+1)) ⊗ ns s (m+1)) at ucap
  rw [recip _ nextPos] at ucap
  change u = v ⊞ (a ⊗ ratio s inv (m-d) m) at hu
  rw [hu] at ucap
  have est := local_budgets s p J v a (ratio s inv (m-d) m) (ratio s inv m (m+1)) k old new A B K
    (fun i _ => hp i) (keys_cap mask) hv hr ucap ac kc bc bn (feed_split s inv recip w d m live)
  dsimp only at est
  rw [←hu] at est; exact est

/-- Express the uniform caps in units of 1/n. zeta is a positive lower
bound for (N-t-1)/n, including the last transition before the cut. -/
theorem scale_caps (inv : α → α) (recip : ∀ a, a ≠ s.zero → inv a ⊗ a = s.one)
    (n N : Nat) (pi zeta M : α) (sn : ns s n ≠ s.zero) (sz : zeta ≠ s.zero)
    (span : N ≤ 2*n) (piCap : (ns s n ⊗ pi) ≼ M) :
    let A := inv (ns s n ⊗ zeta)
    let K := (pi ⊗ cube s (ns s N)) ⊗ quart s A
    let bound := (M ⊗ cube s (ns s 2)) ⊗ quart s (inv zeta)
    (ns s n ⊗ A = inv zeta) ∧ ((ns s n ⊗ ns s n) ⊗ K) ≼ bound ∧
      (ns s n ⊗ (ns s N ⊗ K)) ≼ (ns s 2 ⊗ bound) := by
  intro A K bound
  have hA : ns s n ⊗ A = inv zeta := by
    dsimp only [A]; rw [inverse_product s inv recip sn sz,←s.mulAssoc,s.mulComm (ns s n) (inv (ns s n)),recip _ sn,s.oneMul]
  have cubeMono {x y : α} (h : x ≼ y) : cube s x ≼ cube s y := s.mulMono (s.mulMono h h) h
  have scaleN := le_times s span s.one
  change ns s N ≼ ns s (2*n) at scaleN; rw [size_mult] at scaleN
  have raw := s.mulMono (s.refl (ns s n ⊗ ns s n))
    (s.mulMono (s.mulMono (s.refl pi) (cubeMono scaleN)) (s.refl (quart s A)))
  have eq : ((ns s n ⊗ ns s n) ⊗ ((pi ⊗ cube s (ns s 2 ⊗ ns s n)) ⊗ quart s A)) =
      ((ns s n ⊗ pi) ⊗ cube s (ns s 2)) ⊗ quart s (ns s n ⊗ A) := by unfold quart cube; ac_rfl
  rw [eq,hA] at raw
  have budget := s.trans raw (s.mulMono (s.mulMono piCap (s.refl _)) (s.refl _))
  refine ⟨hA,budget,?_⟩
  have enlarge := s.mulMono (s.refl (ns s n)) (s.mulMono scaleN (s.refl K))
  have rearr : ns s n ⊗ ((ns s 2 ⊗ ns s n) ⊗ K) = ns s 2 ⊗ ((ns s n ⊗ ns s n) ⊗ K) := by ac_rfl
  rw [rearr] at enlarge; exact s.trans enlarge (s.mulMono (s.refl _) budget)

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.before_cut
#print axioms ArticuloA.Trayectoria.Adjunto.scale_caps
