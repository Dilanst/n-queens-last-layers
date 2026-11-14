import Grados

namespace ArticuloA.Repair

/-- Physical candidate for a fixed root, even when the root is not empty.
The two target squares must be compatible with each other (the paper's G filter). -/
def Candidate {n} (p : Placement n) (z e : Cell n) : Prop :=
  let a := corners (z,e)
  e ∈ queens p ∧ compatible a.1 a.2 ∧ freeDiagonals p a.1 ∧ freeDiagonals p a.2

open Classical in
noncomputable def indicator (P : Prop) : Nat := if P then 1 else 0

noncomputable def physicalCount {n} (p : Placement n) (z : Cell n) : Nat :=
  counting.over (board n) (fun e => indicator (Candidate p z e))

private theorem legal_from_pairs {n} (p : Placement n)
    (all : ∀ x ∈ queens p, ∀ y ∈ queens p, x ≠ y → compatible x y) : Legal p := by
  have sub {xs} (b : @Mask (Cell n) xs) : (queens b).Sublist xs := by
    induction b with
    | empty => exact .slnil
    | skip _ ih => exact .cons _ ih
    | take _ ih => exact .cons₂ _ ih
  exact (List.Pairwise.sublist (sub p) (board_unique n)).imp_of_mem
    (fun hx hy hne => all _ hx _ hy hne)

private theorem compat_symm {n} {x y : Cell n} (h : compatible x y) : compatible y x :=
  ⟨Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2⟩

theorem direct_iff_candidate {n} (p : Placement n) (z e : Cell n)
    (hp : Legal p) (hz : emptyCross p z) :
    Direct (pieces p) p (z,e) ↔ Candidate p z e := by
  by_cases old : e ∈ queens p
  case neg => simp [Direct, Candidate,old]
  let m : Mark n := (z,e)
  let a := (corners m).1
  let b := (corners m).2
  let u := forward m p
  have rows := (hz e old).1
  have cols := (hz e old).2
  have ae : a ≠ e := fun eq => rows (by have v := congrArg Prod.fst eq; exact v.symm)
  have be : b ≠ e := fun eq => cols (by have v := congrArg Prod.snd eq; exact v.symm)
  have ab : a ≠ b := fun eq => rows (by have v := congrArg Prod.fst eq; exact v.symm)
  have a0 : a ∉ queens p := fun he => (hz a he).1 rfl
  have b0 : b ∉ queens p := fun he => (hz b he).2 rfl
  have state (x : Cell n) : x ∈ queens u ↔ x = a ∨ x = b ∨ (x ∈ queens p ∧ x ≠ e) := by
    change x ∈ queens (toggle b (toggle a (toggle e p))) ↔ _
    by_cases xa : x = a
    · subst x; simp [mem_toggle, ab, ae, a0]
    by_cases xb : x = b
    · subst x; simp [mem_toggle, Ne.symm ab, be, b0]
    by_cases xe : x = e <;> simp_all [mem_toggle]
  have au := (state a).mpr (Or.inl rfl)
  have bu := (state b).mpr (Or.inr (Or.inl rfl))
  have own : diagonalOK e a ∧ diagonalOK e b := by
    have rv : e.1.val ≠ z.1.val := fun v => rows (Fin.ext v)
    have cv : e.2.val ≠ z.2.val := fun v => cols (Fin.ext v)
    simp only [diagonalOK,a,b,corners,m]; omega
  constructor
  · intro d
    have hu : Legal u := d.2.2.2.2
    refine ⟨old, legal_pair hu au bu ab, ?_, ?_⟩
    · intro x hx
      by_cases xe : x = e
      · subst x; exact own.1
      · exact (legal_pair hu ((state x).mpr (.inr (.inr ⟨hx,xe⟩))) au
                (fun eq => a0 (eq ▸ hx))).2.2
    · intro x hx
      by_cases xe : x = e
      · subst x; exact own.2
      · exact (legal_pair hu ((state x).mpr (.inr (.inr ⟨hx,xe⟩))) bu
                (fun eq => b0 (eq ▸ hx))).2.2
  · rintro ⟨_, between, clearA, clearB⟩
    have withA {x} (hx : x ∈ queens p) (xe : x ≠ e) : compatible x a :=
      ⟨(hz x hx).1,(legal_pair hp hx old xe).2.1, clearA x hx⟩
    have withB {x} (hx : x ∈ queens p) (xe : x ≠ e) : compatible x b :=
      ⟨(legal_pair hp hx old xe).1,(hz x hx).2, clearB x hx⟩
    refine ⟨rfl,hp,hz,old,legal_from_pairs u ?_⟩
    intro x hx y hy xy
    rcases (state x).mp hx with xa | xb | ⟨xo,xe⟩ <;>
      rcases (state y).mp hy with ya | yb | ⟨yo,ye⟩
    · exact (xy (xa.trans ya.symm)).elim
    · simpa only [xa,yb] using (show compatible a b from between)
    · rw [xa]; exact compat_symm (withA yo ye)
    · rw [xb,ya]; exact compat_symm between
    · exact (xy (xb.trans yb.symm)).elim
    · rw [xb]; exact compat_symm (withB yo ye)
    · rw [ya]; exact withA xo xe
    · rw [yb]; exact withB xo xe
    · exact legal_pair hp xo yo xy

theorem physical_eq_crossDegree {n} (p : Placement n) (z : Cell n)
    (hp : Legal p) (hz : emptyCross p z) : physicalCount p z = crossDegree (pieces p) p z := by
  unfold physicalCount crossDegree
  apply congrArg (counting.over (board n))
  funext e
  have eq := direct_iff_candidate p z e hp hz
  by_cases h : Candidate p z e
  · simp [indicator, directWeight, h, eq.mpr h]
  · have no : ¬ Direct (pieces p) p (z,e) := fun d => h (eq.mp d)
    simp [indicator, directWeight, h, no, counting]

end ArticuloA.Repair
#print axioms ArticuloA.Repair.physical_eq_crossDegree
