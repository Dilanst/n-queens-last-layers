import MediaExteriorDeLaInversa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open MeasureTheory Filter Set Perfil
open scoped Interval Topology
def mediaDeCentros (n : ℕ) (f : ℝ→ℝ) := (∑ i : Fin n,f (medio n i.val))/(n:ℝ)

theorem error_de_centros_por_oscilacion {n : ℕ} (hn : 0<n) (f : ℝ→ℝ) (hf : ContinuousOn f unidadCerrada)
    (d : ℝ) (osc : ∀ x∈unidadCerrada,∀ y∈unidadCerrada,|x-y|≤1/(n:ℝ) → |f x-f y|≤d) :
    |(∫ x in (0:ℝ)..1,f x)-mediaDeCentros n f|≤d := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  let m:=fun i : ℕ => (i:ℝ)/n
  have first : m 0=0 := by simp [m]
  have last : m n=1 := by simp [m,np.ne']
  have width (i : ℕ) : m (i+1)-m i=1/n := by dsimp [m]; push_cast; ring
  have inc (i : ℕ) : m i≤m (i+1) := by rw [←sub_nonneg,width]; positivity
  have incl (i : ℕ) (hi : i<n) : Icc (m i) (m (i+1))⊆unidadCerrada := by
    intro x hx
    exact ⟨(div_nonneg (Nat.cast_nonneg _) np.le).trans hx.1,hx.2.trans ((div_le_one np).mpr (by exact_mod_cast hi))⟩
  have inside (i : ℕ) : medio n i∈Icc (m i) (m (i+1)) := by
    dsimp [medio,m]; push_cast; constructor <;> apply div_le_div_of_nonneg_right _ np.le <;> linarith
  have ig (i : ℕ) (hi : i<n) : IntervalIntegrable f volume (m i) (m (i+1)) :=
    (hf.mono (incl i hi)).intervalIntegrable_of_Icc (inc i)
  have est (i : ℕ) (hi : i<n) : |(∫ x in (m i)..(m (i+1)),f x)-1/n*f (medio n i)|≤d*(1/n) := by
    have diff : (∫ x in (m i)..(m (i+1)),f x-f (medio n i))=
        (∫ x in (m i)..(m (i+1)),f x)-1/n*f (medio n i) := by
      rw [intervalIntegral.integral_sub (ig i hi) intervalIntegrable_const,intervalIntegral.integral_const,smul_eq_mul,width]
    rw [←diff]
    have D (x : ℝ) (hx : x∈uIoc (m i) (m (i+1))) : ‖f x-f (medio n i)‖≤d := by
      rw [uIoc_of_le (inc i)] at hx
      have X : x∈Icc (m i) (m (i+1)) := ⟨hx.1.le,hx.2⟩
      apply osc _ (incl i hi X) _ (incl i hi (inside i))
      rw [←width i,abs_le]; constructor <;> linarith only [X.1,X.2,(inside i).1,(inside i).2]
    have res:=intervalIntegral.norm_integral_le_of_norm_le_const D
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (inc i)),width] at res
    exact res
  have add:=intervalIntegral.sum_integral_adjacent_intervals (a:=m) ig
  rw [first,last] at add
  unfold mediaDeCentros
  rw [Finset.sum_range] at add
  rw [←add,Finset.sum_div,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have est':= Finset.sum_le_sum (s:=Finset.range n) (fun i hi => est i (Finset.mem_range.mp hi))
  rw [Finset.sum_range] at est'
  convert est' using 1
  · simp only [one_div,div_eq_inv_mul,mul_one]
  · simp [nsmul_eq_mul,np.ne',mul_comm,one_div,mul_left_comm]

def mediaEspacialDeCentros (n : ℕ) (t : ℝ×ℝ→ℝ) :=
  mediaExterior (fun z : Cell n => t (medio n z.1.val,medio n z.2.val))

theorem media_espacial_iterada (n : ℕ) (t : ℝ×ℝ→ℝ) :
    mediaEspacialDeCentros n t=mediaDeCentros n (fun x => mediaDeCentros n (fun y => t (x,y))) := by
  unfold mediaEspacialDeCentros mediaExterior mediaDeCentros
  rw [Fintype.sum_prod_type,←Finset.sum_div]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_centros_por_oscilacion
#print axioms ArticuloA.Historias.media_espacial_iterada
