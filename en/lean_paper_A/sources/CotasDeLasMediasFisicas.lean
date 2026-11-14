import LeyUniformeDelTablero
namespace ArticuloA.Limites
open Repair
noncomputable section

private theorem sobre_lista {β : Type} (l : List β) (f : β → ℝ) (g : β → ℕ) (M : ℝ)
    (pt : ∀ b, |f b| ≤ M*(g b:ℝ)) :
    |sumReal.over l f| ≤ M*(counting.over l g:ℝ) := by
  induction l with
  | nil => simp [SumLaw.over,sumReal,counting]
  | cons b l ih =>
    change |f b+sumReal.over l f| ≤ M*((g b+counting.over l g:ℕ):ℝ)
    rw [Nat.cast_add,mul_add]
    exact (abs_add_le _ _).trans (add_le_add (pt _) ih)

private theorem sobre_marcas {n} (f : Mark n → ℝ) (g : Mark n → ℕ) (M : ℝ)
    (pt : ∀ m, |f m| ≤ M*(g m:ℝ)) : |sumReal.marks f| ≤ M*(counting.marks g:ℝ) := by
  unfold SumLaw.marks
  apply sobre_lista; intro r
  apply sobre_lista; intro c
  apply sobre_lista; intro i
  apply sobre_lista; intro j
  exact pt _

def Dobs (n h : ℕ) (w : Cell n → ℝ) (p : Placement n) :=
  sumReal.marks (directWeight sumReal (n-h) w p) / ((h:ℝ)^2*n)
def Iobs (n h : ℕ) (w : Cell n → ℝ) (p : Placement n) :=
  sumReal.marks (diagonalWeight sumReal (n-h) w p) / (n:ℝ)^2

theorem directa_acotada (n h : ℕ) (nh : h ≤ n) (hh : 0<h) (w : Cell n → ℝ) (M : ℝ)
    (hm : 0≤M) (cap : ∀ e, |w e|≤M) (p : Placement n) (mem : p ∈ nivel n (n-h)) : |Dobs n h w p| ≤ M := by
  classical
  have pair := (Finset.mem_filter.mp mem).2
  have nn : 0<n := by omega
  have d := directDegree_le p pair.1 pair.2
  rw [show n-(n-h)=h by omega] at d
  have step : directDegree (n-h) p ≤ h^2*n := d.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have H : |sumReal.marks (directWeight sumReal (n-h) w p)| ≤ M*(directDegree (n-h) p:ℝ) := by
    apply sobre_marcas; intro a
    classical
    by_cases e : Direct (n-h) p a <;> simp [directWeight,counting,sumReal,e,cap]
  have bound : (directDegree (n-h) p:ℝ) ≤ (h:ℝ)^2*n := by exact_mod_cast step
  unfold Dobs
  rw [abs_div,abs_of_nonneg (by positivity : 0≤(h:ℝ)^2*n)]
  exact (div_le_iff₀ (by positivity)).mpr (H.trans (mul_le_mul_of_nonneg_left bound hm))

theorem inversa_acotada (n h : ℕ) (nh : h ≤ n) (hh : 0<h) (w : Cell n → ℝ) (M : ℝ)
    (hm : 0≤M) (cap : ∀ e, |w e|≤M) (p : Placement n) (mem : p ∈ nivel n (n-h+1)) : |Iobs n h w p| ≤ M := by
  classical
  have pair := (Finset.mem_filter.mp mem).2
  have nn : 0<n := by omega
  have d := inverseDegree_le (q:=n-h) p
  simp [layer,pair] at d
  have step : inverseDegree (n-h) p ≤ n*n := d.trans (Nat.mul_le_mul (by omega) (by omega))
  have H : |sumReal.marks (diagonalWeight sumReal (n-h) w p)| ≤ M*(inverseDegree (n-h) p:ℝ) := by
    apply sobre_marcas; intro a
    classical
    have equiv : Inverse (n-h) p a ↔ pieces p = n-h+1 ∧ Legal p ∧ a.1 ≠ a.2 ∧
        a.1 ∈ queens p ∧ a.2 ∈ queens p ∧ freeDiagonals p (corners a).2 := by
      constructor <;> rintro ⟨sz,hp,ne,i,j,rest⟩
      · exact ⟨sz,hp,ne,i,j,(inverse_diagonals p a sz hp ne i j).mp ⟨sz,hp,ne,i,j,rest⟩⟩
      · exact (inverse_diagonals p a sz hp ne i j).mpr rest
    by_cases e : Inverse (n-h) p a
    · simp [diagonalWeight,inverseWeight,counting,sumReal,e,equiv.mp e,cap]
    · rw [diagonalWeight,if_neg (mt equiv.mpr e),inverseWeight,if_neg e]; simp [counting,sumReal]
  have bound : (inverseDegree (n-h) p:ℝ) ≤ (n:ℝ)^2 := by rw [pow_two]; exact_mod_cast step
  unfold Iobs
  rw [abs_div,abs_of_nonneg (sq_nonneg (n:ℝ))]
  exact (div_le_iff₀ (by positivity)).mpr (H.trans (mul_le_mul_of_nonneg_left bound hm))
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.directa_acotada
#print axioms ArticuloA.Limites.inversa_acotada
