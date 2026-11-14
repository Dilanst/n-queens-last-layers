import DefectoDelAdjunto
namespace ArticuloA.Trayectoria.Adjunto
open ArticuloA.Corte E2.Regular Control
variable {α ι : Type} (s : ProfileScale α)
local infixl:70 " ⊗ " => s.mul
local infixl:65 " ⊞ " => s.add
local infix:50 " ≼ " => s.le

theorem pair_cap (j : Nat) (h : j ≤ 4) : pairsN j ≤ 6 := by
  have t : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases t with rfl|rfl|rfl|rfl|rfl <;> decide

theorem local_budgets (p : ι → α) (J : List ι) (v a tail r k old new A B K : α)
    (hp : ∀ i ∈ J, p i ≼ s.one) (len : J.length ≤ 4)
    (hv : v ⊞ tail = s.one) (hr : r ⊞ a = s.one)
    (hu : (v ⊞ (a ⊗ tail)) ≼ s.one) (ac : a ≼ A)
    (kc : k ≼ K) (bo : old ≼ B) (bn : new ≼ B)
    (split : old = k ⊞ (quart s r ⊗ new)) :
    let g := a ⊗ tail
    let C := coeff s p v J
    let row := ns s J.length ⊗ a
    let pred := a ⊗ predecessor s (coeff s p v) p J
    let oldC := coeff s p (v ⊞ g) J
    let R := (A ⊗ A) ⊗ ns s 6
    let F := K ⊞ ((ns s 4 ⊗ A) ⊗ B)
    let G := A ⊗ ns s 4
    within s (oldC ⊞ (row ⊗ C)) (C ⊞ pred) R ∧
    within s ((old ⊗ oldC) ⊞ (((s.times 4 a ⊞ row) ⊗ new) ⊗ C))
      (((new ⊗ C) ⊞ (new ⊗ pred)) ⊞ (k ⊗ C)) ((F ⊗ G) ⊞ ((B ⊗ R) ⊞ (R ⊗ B))) ∧
    within s oldC C G ∧ within s (old ⊗ oldC) (new ⊗ C) ((B ⊗ G) ⊞ F) := by
  intro g C row pred oldC R F G
  have vle : v ≼ s.one := hv ▸ up_left s v tail
  have tle : tail ≼ s.one := by rw [s.comm] at hv; exact hv ▸ up_left s tail v
  have rle : r ≼ s.one := hr ▸ up_left s r a
  have gle : g ≼ A := by simpa [g,s.mulOne] using s.mulMono ac tle
  obtain ⟨weak,ch,sc⟩ := caps s p v (v ⊞ g) J hp vle hu
  have red := s.trans sc (le_times s (pair_cap J.length len) s.one)
  have rem := s.mulMono (s.mulMono gle gle) red
  have inc := s.mulMono gle (s.trans (slope_cap s p v J hp vle) (le_times s len s.one))
  have chordBound := s.mulMono gle (s.trans ch (le_times s len s.one))
  have f := s.mono kc (s.mulMono (s.mulMono (s.refl (ns s 4)) ac) bn)
  rw [←times_m] at f
  have four := (size_geom s r rle 4).2.2
  have e4 := s.mulMono (s.mulMono (s.mulMono (s.mulMono ac ac) four) bn) weak
  rw [s.mulOne] at e4
  have addErr {x y b : α} (err : y ≼ b) : within s (x ⊞ y) x b :=
    ⟨s.mono (s.refl x) err,s.trans (up_left s x y) (up_left s _ b)⟩
  have occ := occupied_residue s p v a tail hv J
  have mov : within s oldC C G := by
    dsimp only [oldC]; rw [chord_eq]; exact addErr chordBound
  have avail := available_residue s p v a tail r old new k hv hr split J
  refine ⟨?_,grow s avail (s.mono (s.mulMono f inc) (s.mono (s.mulMono bo rem) e4)),mov,?_⟩
  · dsimp only [oldC,row,C,pred]; rw [occ]; exact addErr rem
  · have h := product_error s (grow s (feed_change s split hr) f) mov
    obtain ⟨small,_,_⟩ := caps s p (v ⊞ g) (v ⊞ g) J hp hu hu
    have out := s.mono (s.mulMono small (s.refl F)) (s.mulMono bn (s.refl G))
    rw [s.oneMul,s.comm F] at out
    exact grow s h out

end ArticuloA.Trayectoria.Adjunto
#print axioms ArticuloA.Trayectoria.Adjunto.local_budgets
