import DeLaDerivaALaSalida
namespace ArticuloA.RealFinita
noncomputable section

theorem prefactor_del_corte (c : ℝ) (cp : 0<c) :
    ∃ n₀ : ℕ,∀ n≥n₀,∀ T≤2*n,
      (6+4*(↑(2*n-1):ℝ))*(T+1)*(2*Real.exp (-(c*n)))≤Real.exp (-(c/2*n)) := by
  obtain ⟨N,grow⟩:=exists_nat_gt (84*48/c^3)
  refine ⟨max 2 N,?_⟩
  intro n hn T hT
  have np : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have t : (T:ℝ)≤2*n := by exact_mod_cast hT
  have d : (↑(2*n-1):ℝ)≤2*n := by exact_mod_cast (by omega : 2*n-1≤2*n)
  have big : 84*48/c^3 ≤ (n:ℝ) := grow.le.trans (by exact_mod_cast (le_max_right 2 N).trans hn)
  have poly : (6+4*(↑(2*n-1):ℝ))*(T+1)*2≤84*(n:ℝ)^2 := by
    have a : 6+4*(↑(2*n-1):ℝ)≤14*n := by linarith
    have b : (T:ℝ)+1≤3*n := by linarith
    have w:=mul_le_mul a b (by positivity) (by positivity); nlinarith only [w]
  have grow' := (div_le_iff₀ (pow_pos cp 3)).mp big
  have cub := mul_le_mul_of_nonneg_right grow' (sq_nonneg (n:ℝ))
  have aux := Real.pow_div_factorial_le_exp (c/2*(n:ℝ)) (show 0≤c/2*(n:ℝ) by positivity) 3
  norm_num [Nat.factorial] at aux
  have expBound : 84*(n:ℝ)^2≤Real.exp (c/2*n) := by nlinarith only [cub,aux]
  calc _ = ((6+4*(↑(2*n-1):ℝ))*(T+1)*2)*Real.exp (-(c*n)) := by ring
       _ ≤ Real.exp (c/2*n)*Real.exp (-(c*n)) :=
          mul_le_mul_of_nonneg_right (poly.trans expBound) (Real.exp_nonneg _)
       _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem eleccion_del_umbral (A B ε : ℝ) (a0 : 0≤A) (bp : 0<B) (ep : 0<ε) :
    ∃ θ α c : ℝ,∃ n₀ : ℕ,0<θ ∧ 0<α ∧ 0<c ∧ θ*B≤1 ∧ ∀ n≥n₀,∀ T≤2*n,
      (α*n+1)*Real.exp (T*(A/n))<ε*n ∧
      (6+4*(↑(2*n-1):ℝ))*(T+1)*(2*Real.exp (T*(θ*B)^2-θ*(α*n)))≤Real.exp (-(c*n)) := by
  let d:=Real.exp (2*A)
  let α:=ε/(2*d)
  have dp : 0<d := Real.exp_pos _
  have ap : 0<α := div_pos ep (by positivity)
  obtain ⟨θ,c,tp,cp,small,ex⟩:=exponente_hasta_el_corte B α bp ap
  obtain ⟨n₁,pref⟩:=prefactor_del_corte c cp
  obtain ⟨n₂,room⟩:=exists_nat_gt (2*d/ε)
  refine ⟨θ,α,c/2,max n₁ (max 1 n₂),tp,ap,by positivity,small,?_⟩
  intro n hn T tT
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have rn : 2*d/ε<(n:ℝ) := room.trans_le (by exact_mod_cast (by omega : n₂≤n))
  have room' := (div_lt_iff₀ ep).mp rn
  have bound : (T:ℝ)*(A/n)≤2*A := by
    have hT : (T:ℝ)≤2*n := by exact_mod_cast tT
    calc _ ≤ (2*n)*(A/n) := mul_le_mul_of_nonneg_right hT (div_nonneg a0 np.le)
         _ = _ := by field_simp; ring
  constructor
  · calc _ ≤ (α*n+1)*d := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr bound) (by positivity)
         _ = ε*n/2+d := by dsimp only [α]; field_simp; ring
         _ < _ := by linarith
  · have b:=Real.exp_le_exp.mpr (ex n T tT)
    apply le_trans _ (pref n (by omega) T tT)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left b (by norm_num)
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.eleccion_del_umbral
