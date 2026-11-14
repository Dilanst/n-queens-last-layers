import NormalizacionReal
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
namespace ArticuloA.Limites
open Repair
noncomputable section
def probBuena (n h : ℕ) (G : Placement n → Prop) : ℝ :=
  eventCount h G / (count n (n-h):ℝ)

/-- Finite version of the last line of §7, with the physical repair degree
at each of the h² final empty crosses. The real threshold needs no rounding loss. -/
theorem desde_cruces (n h : ℕ) (hh : 0<h) (hq : 0<n-h) (nz : 0<count n (n-h))
    (a : ℝ) (G : Placement n → Prop)
    (many : ∀ p, Legal p → pieces p=n-h → G p → ∀ z, emptyCross p z →
      a*n ≤ (crossDegree (n-h) p z : ℝ)) :
    a*(n:ℝ)/(n-h:ℕ)*probBuena n h G ≤ fracReal n h := by
  let t : ℕ := ⌈a*n⌉₊
  let q := n-h
  have natBound := cota_evento_cruda n h t G (by
    intro p hp size ok
    have u := many_of_each_cross p hp size t (fun z hz => Nat.ceil_le.mpr (many p hp size ok z hz))
    simpa only [show n-(n-h)=h by omega] using u)
  have hd : 0 < (h:ℝ) := by exact_mod_cast hh
  have hN : 0 < (count n q:ℝ) := by exact_mod_cast nz
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have H : (eventCount h G:ℝ)*((h:ℝ)^2*t) ≤ (count n (q+1):ℝ)*(((q+1:ℕ):ℝ)*q) := by
    exact_mod_cast natBound
  have HU : (eventCount h G:ℝ)*((h:ℝ)^2*(a*n)) ≤ _ :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Nat.ceil_le.mp (Nat.le_refl t)) (sq_nonneg _))
      (Nat.cast_nonneg _)) H
  unfold probBuena fracReal
  change (a*(n:ℝ)/(q:ℝ))*((eventCount h G:ℝ)/(count n q:ℝ)) ≤
    ((q+1:ℕ):ℝ)*(count n (q+1):ℝ) / ((h:ℝ)^2 * (count n q:ℝ))
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hq' hN) (mul_pos (sq_pos_of_pos hd) hN)]
  calc _ = ((eventCount h G:ℝ)*((h:ℝ)^2*(a*n))) * (count n q:ℝ) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right HU hN.le
       _ = _ := by ring
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.desde_cruces
