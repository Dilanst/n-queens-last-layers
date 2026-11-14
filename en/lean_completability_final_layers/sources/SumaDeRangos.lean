import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators
namespace ArticuloA.Rangos
noncomputable section

private theorem tel {f g : ℕ → ℝ} (K L : ℕ) (h : ∀ m, K≤m → f m≤g (m+1)-g m) :
    ∑ j ∈ Finset.range L, f (K+j) ≤ g (K+L)-g K := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ,Nat.add_succ]
    linarith [h (K+L) (Nat.le_add_right _ _)]

private def prim (D : ℕ) (t : ℕ) : ℝ := t*Real.log ((t:ℝ)/D)-t

private theorem paso_log {D m : ℕ} (hm : 0<m) (hd : 0<D) :
    Real.log ((m:ℝ)/D) ≤ prim D (m+1) - prim D m := by
  have M : 0<(m:ℝ) := by exact_mod_cast hm
  have D' : 0<(D:ℝ) := by exact_mod_cast hd
  have p : 0<(m:ℝ)+1 := by positivity
  have b := Real.log_le_sub_one_of_pos (div_pos M p)
  rw [Real.log_div M.ne' p.ne'] at b
  have b' := mul_le_mul_of_nonneg_left b p.le
  have eq : ((m:ℝ)+1)*(m/(m+1)-1) = -1 := by field_simp
  rw [eq] at b'
  simp only [prim,Nat.cast_add,Nat.cast_one,Real.log_div M.ne' D'.ne',Real.log_div p.ne' D'.ne']
  linarith

theorem suma_log_recortada {K D : ℕ} (hK : 0<K) (le : K≤D) :
    ∑ m ∈ Finset.range (D+1), Real.log ((max m K:ℕ)/ (D:ℝ)) ≤ -(D:ℝ)+K := by
  have d : 0<D := lt_of_lt_of_le hK le
  have d' : (D:ℝ)≠0 := by exact_mod_cast d.ne'
  rw [Finset.sum_range_succ,max_eq_left le,div_self d',Real.log_one,add_zero]
  let f := fun m : ℕ => Real.log ((max m K:ℕ)/(D:ℝ))
  change ∑ m ∈ Finset.range D, f m ≤ _
  have split := Finset.sum_range_add f K (D-K)
  rw [Nat.add_sub_of_le le] at split
  rw [split]
  have head : ∑ m ∈ Finset.range K, f m = (K:ℝ)*Real.log ((K:ℝ)/D) := by
    calc
      _ = ∑ _m ∈ Finset.range K, Real.log ((K:ℝ)/D) := Finset.sum_congr rfl (fun _ hm => by simp only [f,max_eq_right (Finset.mem_range.mp hm).le])
      _ = _ := by simp
  have tail := tel (f:=f) (g:=prim D) K (D-K) (fun m ge => by
    simpa only [f,max_eq_left ge] using paso_log (lt_of_lt_of_le hK ge) d)
  rw [Nat.add_sub_of_le le] at tail
  simp only [prim,div_self d',Real.log_one,mul_zero,zero_sub] at tail
  rw [head]; linarith

private theorem paso_inverso {K m : ℕ} (hk : 0<K) (le : K≤m) :
    (1:ℝ)/(m:ℝ)^3 ≤ (2/(K:ℝ))*(1/(m:ℝ)-1/((m:ℝ)+1)) := by
  have k : 0<(K:ℝ) := by exact_mod_cast hk
  have m' : (K:ℝ)≤m := by exact_mod_cast le
  have uno : (1:ℝ)≤m := by exact_mod_cast (lt_of_lt_of_le hk le)
  have M : 0<(m:ℝ) := by linarith
  have cond : (K:ℝ)*(m+1) ≤ 2*m^2 := by
    nlinarith [mul_le_mul_of_nonneg_right m' (show 0≤(m:ℝ)+1 by positivity),
      mul_nonneg M.le (sub_nonneg.mpr uno)]
  have eq : (2/(K:ℝ))*(1/(m:ℝ)-1/((m:ℝ)+1)) = 2/((K:ℝ)*m*(m+1)) := by field_simp; ring
  rw [eq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left cond M.le]

theorem suma_inversos_recortada {K D : ℕ} (hK : 0<K) (le : K≤D) :
    ∑ m ∈ Finset.range (D+1), (1:ℝ)/((max m K:ℕ):ℝ)^3 ≤ 3/(K:ℝ)^2 := by
  let f := fun m : ℕ => (1:ℝ)/((max m K:ℕ):ℝ)^3
  let g := fun m : ℕ => -(2/(K:ℝ))*(1/(m:ℝ))
  have k : 0<(K:ℝ) := by exact_mod_cast hK
  have hle : K≤D+1 := by omega
  have split := Finset.sum_range_add f K (D+1-K)
  rw [Nat.add_sub_of_le hle] at split
  change ∑ m ∈ Finset.range (D+1), f m ≤ _
  rw [split]
  have head : ∑ m ∈ Finset.range K, f m = (K:ℝ)*(1/(K:ℝ)^3) := by
    calc
      _ = ∑ _m ∈ Finset.range K,(1:ℝ)/(K:ℝ)^3 := Finset.sum_congr rfl (fun _ hm => by simp only [f,max_eq_right (Finset.mem_range.mp hm).le])
      _ = _ := by simp
  have tail := tel (f:=f) (g:=g) K (D+1-K) (fun m ge => by
    simp only [f,max_eq_left ge,g,Nat.cast_add,Nat.cast_one]
    linarith [paso_inverso hK ge])
  rw [Nat.add_sub_of_le hle] at tail
  have sign : g (D+1)≤0 := by dsimp [g]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  rw [head]
  calc
    _ ≤ (K:ℝ)*(1/(K:ℝ)^3) - g K := by linarith
    _ = _ := by dsimp [g]; field_simp; ring
end
end ArticuloA.Rangos
#print axioms ArticuloA.Rangos.suma_log_recortada
#print axioms ArticuloA.Rangos.suma_inversos_recortada
