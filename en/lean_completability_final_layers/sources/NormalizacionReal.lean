import Mathlib.Data.Real.Basic
import CotaReparaciones
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace ArticuloA.Limites
open Repair
noncomputable section

def sumReal : SumLaw ℝ := ⟨0,(·+·),zero_add,add_comm,add_assoc⟩
def directo (n q : ℕ) (w : Cell n → ℝ) :=
  sumReal.masks (board n) (fun p => sumReal.marks (directWeight sumReal q w p))
def inverso (n q : ℕ) (w : Cell n → ℝ) :=
  sumReal.masks (board n) (fun p => sumReal.marks (diagonalWeight sumReal q w p))

def fracReal (n h : ℕ) : ℝ :=
  ((n-h+1:ℕ):ℝ) * (count n (n-h+1):ℝ) / ((h:ℝ)^2 * (count n (n-h):ℝ))
def mediaD (n h : ℕ) (w : Cell n → ℝ) : ℝ :=
  directo n (n-h) w / ((count n (n-h):ℝ)*(h:ℝ)^2*n)
def mediaI (n h : ℕ) (w : Cell n → ℝ) : ℝ :=
  inverso n (n-h) w / ((count n (n-h+1):ℝ)*(n:ℝ)^2)

theorem relacion_fisica {n h : ℕ} (w : Cell n → ℝ) (hn : n ≠ 0) (hh : h ≠ 0)
    (lo : count n (n-h) ≠ 0) (hi : count n (n-h+1) ≠ 0) :
    fracReal n h * mediaI n h w = (((n-h+1:ℕ):ℝ)/n)* mediaD n h w := by
  have same : directo n (n-h) w = inverso n (n-h) w := paper_double_count sumReal _ w
  have N : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have H : (h:ℝ) ≠ 0 := by exact_mod_cast hh
  have L : (count n (n-h):ℝ) ≠ 0 := by exact_mod_cast lo
  have U : (count n (n-h+1):ℝ) ≠ 0 := by exact_mod_cast hi
  unfold fracReal mediaI mediaD
  rw [same]; field_simp [N,H,L,U]; ring

end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.relacion_fisica
