import Std.Internal.Rat

namespace ArticuloA
open Std.Internal

/-- Recover the positive common divisor removed by the standard rational constructor. -/
private theorem ratio_parts (a b : Nat) (hb : 0 < b) :
    ∃ x g : Nat, (mkRat a b).num = Int.ofNat x ∧
      0 < (mkRat a b).den ∧ 0 < g ∧ x*g = a ∧ (mkRat a b).den*g = b := by
  have nz : b ≠ 0 := by omega
  by_cases unit : a.gcd b = 1
  · refine ⟨a,1, ?_, ?_, by decide, by simp, ?_⟩ <;>
      simp [mkRat, Rat.normalize, nz, unit, hb]
  · refine ⟨a/(a.gcd b), a.gcd b, ?_, ?_, Nat.gcd_pos_of_pos_right a hb,
      Nat.div_mul_cancel (Nat.gcd_dvd_left a b), ?_⟩
    · simp [mkRat, Rat.normalize, nz, unit, Int.ofNat_tdiv]
    · simpa [mkRat, Rat.normalize, nz, unit] using Nat.div_gcd_pos_of_pos_right a hb
    · simpa [mkRat, Rat.normalize, nz, unit] using Nat.div_mul_cancel (Nat.gcd_dvd_right a b)

/-- Comparison of normalized nonnegative rationals, including zero numerators. -/
theorem ratio_le_of_cross {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (cross : a*d ≤ c*b) : mkRat a b ≤ mkRat c d := by
  let l := mkRat a b
  let r := mkRat c d
  obtain ⟨x,g,lx,lb,hg,xa,gb⟩ := ratio_parts a b hb
  obtain ⟨y,j,ry,rd,hj,yc,jd⟩ := ratio_parts c d hd
  change l.num = Int.ofNat x at lx
  change r.num = Int.ofNat y at ry
  change 0 < l.den at lb
  change 0 < r.den at rd
  change l.den*g = b at gb
  change r.den*j = d at jd
  have scaled : x*r.den*(g*j) ≤ y*l.den*(g*j) := by
    calc
      _ = (x*g)*(r.den*j) := by ac_rfl
      _ ≤ (y*j)*(l.den*g) := by simpa only [xa,yc,gb,jd] using cross
      _ = _ := by ac_rfl
  have cmp := Nat.le_of_mul_le_mul_right scaled (Nat.mul_pos hg hj)
  change ¬ (Rat.lt r l = true)
  unfold Rat.lt
  rw [lx,ry]
  by_cases yz : y = 0
  · subst y
    have xz : x = 0 := by
      apply Classical.byContradiction
      intro h
      have := Nat.mul_pos (Nat.pos_of_ne_zero h) rd
      omega
    subst x; simp
  · by_cases xz : x = 0
    · subst x; simp [yz]
    · have notlt : ¬(Int.ofNat y * ((l.den : Int)) < Int.ofNat x * ((r.den : Int))) := by
        exact fun h => (Nat.not_lt_of_ge cmp) (Int.ofNat_lt.mp h)
      have nonzero : (y : Int) ≠ 0 := by omega
      simpa [nonzero, yz, xz] using notlt

end ArticuloA
