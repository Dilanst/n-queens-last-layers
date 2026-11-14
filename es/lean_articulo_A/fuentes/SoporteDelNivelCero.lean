import PesosDeLosDosColores
import PositividadRegional
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Corte Regular ProfileKernel
variable {α : Type} (s : ProfileScale α)

theorem real_del_lleno {n} (r c d a : Nat → α) (e : Cell n)
    (inv : α → α) (recip : ∀ z, z ≠ s.zero → s.mul (inv z) z = s.one)
    (hr : r e.1.val ≠ s.zero) (hc : c e.2.val ≠ s.zero)
    (hd : d (lines e 2) ≠ s.zero) (ha : a (lines e 3) ≠ s.zero) :
    weights s (fullColors s n r c d a).real (lines e) ≠ s.zero := by
  rw [full_real]; exact mul_live s inv recip (mul_live s inv recip hr hc) (mul_live s inv recip hd ha)

theorem virtual_del_lleno {n} (r c d a : Nat → α) (g : Edge)
    (inv : α → α) (recip : ∀ z, z ≠ s.zero → s.mul (inv z) z = s.one)
    (hd : d (g 2) ≠ s.zero) (ha : a (g 3) ≠ s.zero) :
    weights s (fullColors s n r c d a).virtual g ≠ s.zero ↔ n ≤ g 0 ∧ n ≤ g 1 := by
  rw [full_virtual]
  split
  · rename_i phys; constructor <;> intro bad <;> simp_all <;> omega
  · rename_i dummy; exact ⟨fun _ => by omega, fun _ => mul_live s inv recip hd ha⟩

private theorem atom_le_total {X} (L : Atoms α X) (i : α × X) (hi : i ∈ L) :
    s.le i.1 (total s L) := by
  induction L with
  | nil => contradiction
  | cons j xs ih =>
    change s.le i.1 (s.add (s.mul j.1 s.one) (total s xs))
    rw [s.mulOne]
    rcases List.mem_cons.mp hi with eq|mem
    · rw [eq]; exact up_left s _ _
    · rw [s.comm]; exact s.trans (ih mem) (up_left s _ _)

/-- A positive available member of either colour makes that normalizer live;
choose assigns positive mass to this specific member. -/
theorem positive_color_choice {X} (L : Atoms α X) (fallback : X) (i : α × X)
    (mem : i ∈ L) (positive : i.1 ≠ s.zero)
    (inv : α → α) (recip : ∀ z, z ≠ s.zero → s.mul (inv z) z = s.one)
    (proper : ∀ z, s.le z s.zero → z = s.zero) :
    ∃ mass, mass ≠ s.zero ∧ (mass,i.2) ∈ choose s L fallback inv := by
  classical
  have live : total s L ≠ s.zero := by
    intro eq; exact positive (proper _ (eq ▸ atom_le_total s L i mem))
  have one : s.one ≠ s.zero := by
    intro eq; apply positive; have z := s.mulOne i.1; rw [eq,s.mulZero] at z; exact z.symm
  have ip : inv (total s L) ≠ s.zero := by
    intro eq; have id := recip _ live; rw [eq,s.mulComm,s.mulZero] at id; exact one id.symm
  refine ⟨_,mul_live s inv recip ip positive,?_⟩
  rw [choose,if_neg live]; exact List.mem_map.mpr ⟨i,mem,rfl⟩
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.real_del_lleno
#print axioms ArticuloA.Trayectoria.E2.virtual_del_lleno
#print axioms ArticuloA.Trayectoria.E2.positive_color_choice
