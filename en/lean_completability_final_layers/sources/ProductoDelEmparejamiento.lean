import SoporteDelNivelCero
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Corte
variable {α : Type} (s : ProfileScale α)
local instance : Std.Associative s.mul := ⟨s.mulAssoc⟩
local instance : Std.Commutative s.mul := ⟨s.mulComm⟩
local infixl:70 " ⊗ " => s.mul

def producto {ι} (f : ι → α) : List ι → α
  | [] => s.one
  | i::L => f i ⊗ producto f L

theorem reordenar {ι} (f : ι → α) {L J : List ι} (eq : L.Perm J) :
    producto s f L = producto s f J := by
  induction eq with
  | nil => rfl
  | cons x _ ih => simp only [producto,ih]
  | swap => simp only [producto]; ac_rfl
  | trans _ _ ih jh => exact ih.trans jh

private theorem proj {ι β} (g : ι → β) (w : β → α) (xs : List ι) :
    producto s (fun e => w (g e)) xs = producto s w (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons e xs ih => simp only [producto,List.map_cons,ih]

theorem cubierta {ι} (L : List ι) (v : ι → Edge) (N : Nat) (u : Fin 4 → Nat → α)
    (covers : ∀ i, (L.map (fun j => v j i)).Perm (List.range N)) :
    producto s (fun j => weights s u (v j)) L =
    s.four (fun i => producto s (u i) (List.range N)) := by
  have rows (xs : List ι) : producto s (fun j => weights s u (v j)) xs =
      s.four (fun i => producto s (fun j => u i (v j i)) xs) := by
    induction xs with
    | nil => simp [producto,ProfileScale.four,s.oneMul]
    | cons x xs ih =>
      simp only [producto]; rw [ih]; simp only [weights,ProfileScale.four]; ac_rfl
  rw [rows]
  apply congrArg s.four; funext i
  rw [proj s _ (u i) L]; exact reordenar s _ (covers i)

def efectivo (n : Nat) (r c d a : Nat → α) : Fin 4 → Nat → α
  | 0 => fun i => if i<n then r i else s.one
  | 1 => fun i => if i<n then c i else s.one
  | 2 => d
  | 3 => a

inductive Pieza (n : Nat) | real (e : Cell n) | virtual (g : Edge)
def edgeOf {n} : Pieza n → Edge | .real e => lines e | .virtual g => g
def pesoPieza {n} (w : ColorWeights α) : Pieza n → α
  | .real e => weights s w.real (lines e)
  | .virtual g => weights s w.virtual g

theorem producto_lleno {n} (r c d a : Nat → α) (L : List (Pieza n))
    (cubre : ∀ i, (L.map (fun j => edgeOf j i)).Perm (List.range (2*n-1)))
    (dummy : ∀ g, Pieza.virtual g ∈ L → n ≤ g 0 ∧ n ≤ g 1) :
    producto s (pesoPieza s (fullColors s n r c d a)) L =
      s.four (fun i => producto s (efectivo s n r c d a i) (List.range (2*n-1))) := by
  have eq (j : Pieza n) (mem : j ∈ L) : pesoPieza s (fullColors s n r c d a) j =
      weights s (efectivo s n r c d a) (edgeOf j) := by
    cases j with
    | real e => simp [pesoPieza,fullColors,weights,edgeOf,ProfileScale.four,efectivo,lines,e.1.isLt,e.2.isLt]
    | virtual g =>
      obtain ⟨hr,hc⟩ := dummy g mem
      simp [pesoPieza,full_virtual,weights,edgeOf,ProfileScale.four,fullColors,efectivo,Nat.not_lt.mpr hr,
        Nat.not_lt.mpr hc,s.oneMul]
  have substProd {β} (w v : β → α) (xs : List β) (same : ∀ j ∈ xs, w j = v j) :
      producto s w xs = producto s v xs := by
    induction xs with
    | nil => rfl
    | cons i xs ih => rw [producto,producto,same i (by simp),ih (fun j hj => same j (by simp [hj]))]
  exact (substProd _ _ L eq).trans (cubierta s L edgeOf _ _ cubre)
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.cubierta
#print axioms ArticuloA.Trayectoria.E2.producto_lleno
