import CambioCasilla

namespace ArticuloA.Repair

abbrev Mark (n : Nat) := Cell n × Cell n

/-- Converts (cross, old queen) to the ordered pair of new queens, and conversely. -/
def corners {n} (m : Mark n) : Mark n := ((m.1.1, m.2.2), (m.2.1, m.1.2))

@[simp] theorem corners_twice {n} (m : Mark n) : corners (corners m) = m := rfl

def separated {n} (m : Mark n) : Prop := m.1.1 ≠ m.2.1 ∧ m.1.2 ≠ m.2.2

def emptyCross {n} (p : Placement n) (z : Cell n) : Prop :=
  ∀ x ∈ queens p, x.1 ≠ z.1 ∧ x.2 ≠ z.2

def forward {n} (m : Mark n) (p : Placement n) :=
  toggle (corners m).2 (toggle (corners m).1 (toggle m.2 p))

def backward {n} (a : Mark n) (u : Placement n) :=
  toggle (corners a).2 (toggle a.1 (toggle a.2 u))

@[simp] theorem undo {n} (m : Mark n) (p : Placement n) :
    backward (corners m) (forward m p) = p := by simp [backward, forward]

@[simp] theorem redo {n} (a : Mark n) (u : Placement n) :
    forward (corners a) (backward a u) = u := by simp [backward, forward]

def Direct {n} (q : Nat) (p : Placement n) (m : Mark n) : Prop :=
  pieces p = q ∧ Legal p ∧ emptyCross p m.1 ∧ m.2 ∈ queens p ∧ Legal (forward m p)

def Inverse {n} (q : Nat) (u : Placement n) (a : Mark n) : Prop :=
  pieces u = q+1 ∧ Legal u ∧ a.1 ≠ a.2 ∧ a.1 ∈ queens u ∧ a.2 ∈ queens u ∧
    Legal (backward a u)

private theorem separateCells {n} {m : Mark n} (d : separated m) :
    (corners m).1 ≠ m.2 ∧ (corners m).2 ≠ m.2 ∧ (corners m).1 ≠ (corners m).2 := by
  exact ⟨fun e => d.1 (by have v := congrArg Prod.fst e; exact v),
         fun e => d.2 (by have v := congrArg Prod.snd e; exact v),
         fun e => d.1 (by have v := congrArg Prod.fst e; exact v)⟩

theorem forward_valid {n q} {p : Placement n} {m : Mark n} (h : Direct q p m) :
    Inverse q (forward m p) (corners m) := by
  obtain ⟨size, legal, free, old, next⟩ := h
  have sep : separated m := ⟨Ne.symm (free _ old).1, Ne.symm (free _ old).2⟩
  obtain ⟨as',bs',ab⟩ := separateCells sep
  have a0 : (corners m).1 ∉ queens p := fun e => (free _ e).1 rfl
  have b0 : (corners m).2 ∉ queens p := fun e => (free _ e).2 rfl
  have size1 := toggle_size m.2 p
  have size2 := toggle_size (corners m).1 (toggle m.2 p)
  have size3 := toggle_size (corners m).2 (toggle (corners m).1 (toggle m.2 p))
  simp only [mem_toggle, if_neg as', if_neg bs', if_neg (Ne.symm ab),
             if_pos old, if_neg a0, if_neg b0] at size1 size2 size3
  refine ⟨by unfold forward; omega, next, ab, ?_, ?_, by simpa using legal⟩
  · simp [forward, mem_toggle, ab, as', a0]
  · simp [forward, mem_toggle, Ne.symm ab, bs', b0]

theorem backward_valid {n q} {u : Placement n} {a : Mark n} (h : Inverse q u a) :
    Direct q (backward a u) (corners a) := by
  obtain ⟨size, legal, ne, first, second, before⟩ := h
  have comp := legal_pair legal first second ne
  let m := corners a
  have sep : separated m := ⟨comp.1, Ne.symm comp.2.1⟩
  obtain ⟨as',bs',ab⟩ := separateCells sep
  change a.1 ≠ m.2 at as'
  change a.2 ≠ m.2 at bs'
  have old0 : m.2 ∉ queens u := fun e => (legal_pair legal e second (Ne.symm bs')).1 rfl
  have size1 := toggle_size a.2 u
  have size2 := toggle_size a.1 (toggle a.2 u)
  have size3 := toggle_size m.2 (toggle a.1 (toggle a.2 u))
  simp only [mem_toggle, if_neg ne, if_neg (Ne.symm as'), if_neg (Ne.symm bs'),
             if_pos second, if_pos first, if_neg old0] at size1 size2 size3
  refine ⟨by change pieces (toggle m.2 (toggle a.1 (toggle a.2 u))) = q; omega,
          before, ?_, ?_, by simpa using legal⟩
  · intro x hx
    change x ∈ queens (toggle m.2 (toggle a.1 (toggle a.2 u))) at hx
    by_cases xo : x = m.2
    · rw [xo]; exact ⟨Ne.symm sep.1, Ne.symm sep.2⟩
    by_cases xa : x = a.1
    · subst x; simp [mem_toggle, as', ne, first] at hx
    by_cases xb : x = a.2
    · subst x; simp [mem_toggle, bs', Ne.symm ne, second] at hx
    simp [mem_toggle, xo, xa, xb] at hx
    exact ⟨(legal_pair legal hx first xa).1, (legal_pair legal hx second xb).2.1⟩
  · change m.2 ∈ queens (toggle m.2 (toggle a.1 (toggle a.2 u)))
    simp [mem_toggle, Ne.symm as', Ne.symm bs', old0]

abbrev DirectOp (n q : Nat) := {t : Placement n × Mark n // Direct q t.1 t.2}
abbrev InverseOp (n q : Nat) := {t : Placement n × Mark n // Inverse q t.1 t.2}

def toInverse {n q} (o : DirectOp n q) : InverseOp n q :=
  ⟨(forward o.val.2 o.val.1, corners o.val.2), forward_valid o.property⟩

def toDirect {n q} (o : InverseOp n q) : DirectOp n q :=
  ⟨(backward o.val.2 o.val.1, corners o.val.2), backward_valid o.property⟩

theorem direct_roundtrip {n q} (o : DirectOp n q) : toDirect (toInverse o) = o := by
  apply Subtype.ext
  simp [toInverse, toDirect]

theorem inverse_roundtrip {n q} (o : InverseOp n q) : toInverse (toDirect o) = o := by
  apply Subtype.ext
  simp [toInverse, toDirect]

theorem weight_preserved {n q} {α : Type} (w : Cell n → α) (o : DirectOp n q) :
    w (corners (toInverse o).val.2).1 = w o.val.2.1 := rfl

end ArticuloA.Repair
