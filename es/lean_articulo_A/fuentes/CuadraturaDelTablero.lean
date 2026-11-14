import MallaDeLasCuatroFamilias
open MeasureTheory Set
open scoped BigOperators Interval
namespace ArticuloA.Perfil
noncomputable section
abbrev unidadCerrada := Icc (0:ℝ) 1

theorem continua_de_cota {I : Set ℝ} {f : ℝ→ℝ} {L : ℝ} (lp : 0≤L)
    (ine : ∀ x∈I,∀ y∈I,|f x-f y|≤L*|x-y|) : ContinuousOn f I :=
  (LipschitzOnWith.of_dist_le_mul (K:=⟨L,lp⟩) (by simpa only [Real.dist_eq] using ine)).continuousOn

def integralFila (f : ℝ→ℝ→ℝ) (x : ℝ) := ∫ y in (0:ℝ)..1,f x y
def integralTablero (f : ℝ→ℝ→ℝ) := ∫ x in (0:ℝ)..1,integralFila f x
def muestraTablero (n : ℕ) (f : ℝ→ℝ→ℝ) := ∑ i∈Finset.range n,∑ j∈Finset.range n,f (centro n i) (centro n j)

theorem centro_pertenece (n i : ℕ) (hin : i<n) : centro n i∈unidadCerrada := by
  have np : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have z : (i:ℝ)+1≤n := by exact_mod_cast hin
  simp only [centro,nodo,zero_add]; exact ⟨by positivity,(div_le_one np).mpr (by linarith)⟩

theorem cuadratura_dos_dimensiones (n : ℕ) (hn : 0<n) (f : ℝ→ℝ→ℝ) (L : ℝ) (lp : 0≤L)
    (rLip : ∀ x∈unidadCerrada,∀ y∈unidadCerrada,∀ c∈unidadCerrada,|f x c-f y c|≤L*|x-y|)
    (cLip : ∀ x∈unidadCerrada,∀ y∈unidadCerrada,∀ z∈unidadCerrada,|f x y-f x z|≤L*|y-z|) :
    |(n:ℝ)^2*integralTablero f-muestraTablero n f|≤2*L*n := by
  have cg (x) (hx : x∈unidadCerrada) := continua_de_cota lp (cLip x hx)
  have rg (x) (hx : x∈unidadCerrada) (y) (hy : y∈unidadCerrada) :
      |integralFila f x-integralFila f y|≤L*|x-y| := by
    unfold integralFila
    rw [←intervalIntegral.integral_sub ((cg x hx).intervalIntegrable_of_Icc zero_le_one)
      ((cg y hy).intervalIntegrable_of_Icc zero_le_one)]
    have z (c : ℝ) (hc : c∈uIoc (0:ℝ) 1) : ‖f x c-f y c‖≤L*|x-y| := by
      rw [uIoc_of_le zero_le_one] at hc
      exact rLip x hx y hy c ⟨hc.1.le,hc.2⟩
    simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const z
  have outer := cuadratura_centros n hn _ L lp (continua_de_cota lp rg) rg
  have inner (i : ℕ) (hi : i∈Finset.range n) := cuadratura_centros n hn _ L lp
    (cg (centro n i) (centro_pertenece n i (Finset.mem_range.mp hi))) (cLip _ (centro_pertenece n i (Finset.mem_range.mp hi)))
  let G := ∑ i∈Finset.range n,integralFila f (centro n i)
  have a : |(n:ℝ)*((n:ℝ)*integralTablero f-G)|≤(n:ℝ)*L := by
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left outer (Nat.cast_nonneg n)
  have b : |(n:ℝ)*G-muestraTablero n f|≤(n:ℝ)*L := by
    unfold G muestraTablero
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum inner).trans_eq (by simp [nsmul_eq_mul]))
  have eq : (n:ℝ)^2*integralTablero f-muestraTablero n f=
      (n:ℝ)*((n:ℝ)*integralTablero f-G)+((n:ℝ)*G-muestraTablero n f) := by ring
  rw [eq]; exact (abs_add_le _ _).trans (by linarith only [a,b])
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.cuadratura_dos_dimensiones
