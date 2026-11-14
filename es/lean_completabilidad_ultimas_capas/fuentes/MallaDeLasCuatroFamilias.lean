import CuadraturaDeUnaFibra
import Mathlib.Tactic.FieldSimp
open MeasureTheory Set
open scoped BigOperators Interval
namespace ArticuloA.Perfil
noncomputable section

def nodo (a : ℝ) (n i : ℕ) (s : ℝ) := a+((i:ℝ)+s)/n

theorem cuadratura_malla (n M : ℕ) (hn : 0<n) (a t L : ℝ) (t0 : 0≤t) (t1 : t≤1) (lp : 0≤L)
    (f : ℝ→ℝ) (hc : ContinuousOn f (Icc a (a+(M:ℝ)/n)))
    (hl : ∀ x∈Icc a (a+(M:ℝ)/n),∀ y∈Icc a (a+(M:ℝ)/n),|f x-f y|≤L*|x-y|) :
    |(n:ℝ)*(∫ x in a..(a+(M:ℝ)/n),f x)-∑ i∈Finset.range M,f (nodo a n i t)|≤L*((M:ℝ)/n) := by
  have np : (0:ℝ)<n := by exact_mod_cast hn
  let m := fun i : ℕ => a+(i:ℝ)/n
  let z := fun i : ℕ => nodo a n i t
  have step (i : ℕ) : m (i+1)-m i=1/n := by dsimp [m]; push_cast; ring
  have up (i : ℕ) (lt : i<M) : Icc (m i) (m (i+1))⊆Icc a (a+(M:ℝ)/n) := by
    intro x hx
    exact ⟨(le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg i) np.le)).trans hx.1,
      hx.2.trans (add_le_add_left (div_le_div_of_nonneg_right (by exact_mod_cast lt) np.le) a)⟩
  have inc (i : ℕ) : m i≤m (i+1) := by rw [←sub_nonneg,step]; positivity
  have zmem (i : ℕ) : z i∈Icc (m i) (m (i+1)) := by
    dsimp [z,nodo,m]; push_cast
    exact ⟨add_le_add_left (div_le_div_of_nonneg_right (by linarith) np.le) _,
      add_le_add_left (div_le_div_of_nonneg_right (by linarith) np.le) _⟩
  have est := cuadratura_finita M m z f L lp (fun i _ => inc i) (fun i _ => zmem i)
    (fun i hi => (hc.mono (up i hi)).intervalIntegrable_of_Icc (inc i))
    (fun i hi x hx => hl x (up i hi hx) (z i) (up i hi (zmem i)))
  simp only [step,Finset.sum_const,Finset.card_range,nsmul_eq_mul,←Finset.mul_sum] at est
  have eq : m 0=a := by simp [m]
  rw [eq] at est
  have bd := mul_le_mul_of_nonneg_left est np.le
  rw [←abs_of_pos np,←abs_mul] at bd
  convert bd using 1
  · congr 1; dsimp [m,z]; field_simp; ring
  · rw [abs_of_pos np]; field_simp; ring

def centro (n i : ℕ) := nodo 0 n i (1/2)
def interior (a : ℝ) (n i : ℕ) := nodo a n (i+1) 0

theorem cuadratura_centros (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (L : ℝ) (lp : 0≤L)
    (hc : ContinuousOn f (Icc 0 1)) (hl : ∀ x∈Icc 0 1,∀ y∈Icc 0 1,|f x-f y|≤L*|x-y|) :
    |(n:ℝ)*(∫ x in (0:ℝ)..1,f x)-∑ i∈Finset.range n,f (centro n i)|≤L := by
  have nz : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simpa [centro,nz] using cuadratura_malla n n hn 0 (1/2) L (by norm_num) (by norm_num) lp f
    (by simpa [nz] using hc) (by simpa [nz] using hl)

theorem cuadratura_diagonales (n : ℕ) (hn : 0<n) (a : ℝ) (f : ℝ→ℝ) (L : ℝ) (lp : 0≤L)
    (hc : ContinuousOn f (Icc a (a+2))) (hl : ∀ x∈Icc a (a+2),∀ y∈Icc a (a+2),|f x-f y|≤L*|x-y|) :
    |(n:ℝ)*(∫ x in a..(a+2),f x)-∑ i∈Finset.range (2*n-1),f (interior a n i)|≤2*L+|f a| := by
  have np : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have len : ((2*n:ℕ):ℝ)/n=2 := by push_cast; field_simp
  have e := cuadratura_malla n (2*n) hn a 0 L le_rfl zero_le_one lp f (by simpa only [len] using hc)
    (by simpa only [len] using hl)
  simp only [len] at e
  let v := fun i => f (nodo a n i 0)
  have splitS : ∑ i∈Finset.range (2*n),v i = (∑ i∈Finset.range (2*n-1),v (i+1))+v 0 := by
    calc
      _ = ∑ i∈Finset.range ((2*n-1)+1),v i := congrArg (fun t => ∑ i∈Finset.range t,v i) (by omega)
      _ = _ := Finset.sum_range_succ' v (2*n-1)
  have va : v 0=f a := by simp [v,nodo]
  change |(n:ℝ)*_ - ∑ i∈Finset.range (2*n),v i|≤L*2 at e
  rw [splitS,va] at e
  have t := abs_add_le ((n:ℝ)*(∫ x in a..(a+2),f x)-((∑ i∈Finset.range (2*n-1),v (i+1))+f a)) (f a)
  rw [sub_add_eq_sub_sub,sub_add_cancel] at t
  rw [sub_add_eq_sub_sub] at e
  exact t.trans (by linarith)
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.cuadratura_centros
#print axioms ArticuloA.Perfil.cuadratura_diagonales
