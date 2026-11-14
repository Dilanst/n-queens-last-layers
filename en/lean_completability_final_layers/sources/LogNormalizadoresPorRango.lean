import SumaDeRangos
namespace ArticuloA.Rangos
open scoped BigOperators
noncomputable section

private theorem envolvente {u j D c : ℝ} (u0 : 0≤u) (uj : u≤j) (j1 : 1≤j) (d : 0<D) (c0 : 0≤c) :
    (u/D)^4 + c*(u/D)/(D+1) + c/(D+1)^2 ≤ (j/D)^4*(1+2*c*D^2/j^3) := by
  have j0 : 0<j := by linarith
  have dp : 0<D+1 := by positivity
  have a : u/D/(D+1) ≤ j/D^2 := by
    rw [div_div,pow_two]
    exact div_le_div₀ (by positivity) uj (by positivity) (by nlinarith)
  have b : 1/(D+1)^2 ≤ j/D^2 :=
    div_le_div₀ (by positivity) j1 (by positivity) (by nlinarith)
  have eq : (j/D)^4 + c*(j/D^2) + c*(j/D^2) = (j/D)^4*(1+2*c*D^2/j^3) := by field_simp; ring
  rw [←eq]
  exact add_le_add (add_le_add (pow_le_pow_left₀ (div_nonneg u0 d.le) (div_le_div_of_nonneg_right uj d.le) 4)
    (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left a c0))
    (by simpa [←mul_div_assoc] using mul_le_mul_of_nonneg_left b c0)

theorem cota_log_individual {m K D : ℕ} {c W Y : ℝ} (d : 0<D) (k : 0<K)
    (c0 : 0≤c) (wp : 0<W) (yp : 0<Y)
    (envelope : Y/W ≤ ((m:ℝ)/D)^4+c*((m:ℝ)/D)/(D+1)+c/(D+1)^2) :
    Real.log Y ≤ Real.log W + 4*Real.log ((max m K:ℕ)/(D:ℝ)) +
      (2*c*(D:ℝ)^2)*(1/((max m K:ℕ):ℝ)^3) := by
  let j : ℝ := (max m K:ℕ)
  have dk : 0<(D:ℝ) := by exact_mod_cast d
  have j1 : 1≤j := by dsimp only [j]; exact_mod_cast (le_trans k (le_max_right m K))
  have jm : (m:ℝ)≤j := by dsimp only [j]; exact_mod_cast (le_max_left m K)
  have jpos : 0<j := by linarith
  have ub := envelope.trans (envolvente (by positivity) jm j1 dk c0)
  have l := Real.log_le_log (div_pos yp wp) ub
  have nn : 0≤2*c*(D:ℝ)^2/j^3 := by positivity
  have zpos : 0<1+2*c*(D:ℝ)^2/j^3 := by linarith
  have rem := Real.log_le_sub_one_of_pos zpos
  rw [Real.log_div yp.ne' wp.ne',Real.log_mul (by positivity) zpos.ne',Real.log_pow] at l
  change Real.log Y≤Real.log W + 4*Real.log (j/D) + (2*c*(D:ℝ)^2)*(1/j^3)
  rw [←mul_div_assoc,mul_one]
  push_cast at l
  linarith

/-- Sum over ranks. The cutoff condition is integer-valued, including the last rank m=0. -/
theorem suma_normalizadores {D K : ℕ} {c W : ℝ} (k : 0<K) (le : K≤D) (cut : D^2≤K^3)
    (c0 : 0≤c) (wp : 0<W) (Y : ℕ→ℝ) (yp : ∀ m≤D,0<Y m)
    (env : ∀ m≤D, Y m/W≤((m:ℝ)/D)^4+c*((m:ℝ)/D)/(D+1)+c/(D+1)^2) :
    ∑ m ∈ Finset.range (D+1),Real.log (Y m) ≤
      ((D:ℝ)+1)*Real.log W-4*((D:ℝ)+1)+4+(4+6*c)*(K:ℝ) := by
  let p := fun m : ℕ => Real.log ((max m K:ℕ)/(D:ℝ))
  let z := fun m : ℕ => (1:ℝ)/((max m K:ℕ):ℝ)^3
  let a := 2*c*(D:ℝ)^2
  have d : 0<D := lt_of_lt_of_le k le
  have H : 0<(K:ℝ) := by exact_mod_cast k
  have cutR : (D:ℝ)^2≤(K:ℝ)^3 := by exact_mod_cast cut
  have A : 0≤a := by dsimp [a]; positivity
  have last : a*(3/(K:ℝ)^2)≤6*c*K := by
    dsimp [a]; rw [←mul_div_assoc]; apply (div_le_iff₀ (sq_pos_of_pos H)).mpr
    nlinarith [mul_le_mul_of_nonneg_left cutR c0]
  calc
    _ ≤ ∑ m ∈ Finset.range (D+1),(Real.log W+4*p m+a*z m) := Finset.sum_le_sum (fun m hm =>
      cota_log_individual d k c0 wp (yp m (by have := Finset.mem_range.mp hm; omega)) (env m (by have := Finset.mem_range.mp hm; omega)))
    _ = ((D:ℝ)+1)*Real.log W + 4*(∑ m ∈ Finset.range (D+1),p m) + a*(∑ m ∈ Finset.range (D+1),z m) := by
      simp [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by
      have b := mul_le_mul_of_nonneg_left (suma_inversos_recortada k le) A
      change a*(∑ m ∈ Finset.range (D+1),z m)≤_ at b
      have l := suma_log_recortada k le
      change ∑ m ∈ Finset.range (D+1),p m≤_ at l
      linarith
end
end ArticuloA.Rangos
#print axioms ArticuloA.Rangos.suma_normalizadores
