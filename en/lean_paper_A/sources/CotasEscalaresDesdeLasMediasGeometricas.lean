import JensenEnLasMedidasFisicas
namespace ArticuloA.Historias
noncomputable section
/-- Bounds following from the two fibre comparisons and the entropy floor. -/
theorem bandas_de_las_medias {δ b R C E : ℝ} (d : 0<δ) (bp : 0≤b)
    (rp : 0≤R) (cp : 0≤C) (r1 : R≤1) (c1 : C≤1) (e : 1≤E)
    (br : b*R≤δ*E) (bc : b*C≤δ*E) (mass : δ≤b*R*C) :
    δ≤b ∧ b≤δ*E^2 ∧ 1/E≤R ∧ 1/E≤C ∧ δ≤b*R ∧ δ≤b*C := by
  have ep:=zero_lt_one.trans_le e
  have rev : δ≤b*C*R := by linarith only [mass]
  have lower s t (sp : 0≤s) (bst : δ≤b*s*t) (bt : b*t≤δ*E) : 1≤s*E := by
    have h : δ≤δ*(s*E) := by nlinarith only [bst,mul_le_mul_of_nonneg_left bt sp]
    by_contra! u; nlinarith only [h,mul_pos d (sub_pos.mpr u)]
  have drop s t (sp : 0≤s) (t1 : t≤1) (bst : δ≤b*s*t) : δ≤b*s :=
    bst.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left t1 (mul_nonneg bp sp))
  have rb:=lower R C rp mass bc
  have cb:=lower C R cp rev br
  have dr:=drop R C rp c1 mass
  have dc:=drop C R cp r1 rev
  refine ⟨dr.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left r1 bp),?_,
    (div_le_iff₀ ep).mpr rb,(div_le_iff₀ ep).mpr cb,dr,dc⟩
  nlinarith only [mul_le_mul_of_nonneg_left rb bp,mul_le_mul_of_nonneg_right br ep.le]

theorem banda_transversal_desde_el_reciproco {x δ b s E t : ℝ} (xn : 0≤x) (d : δ=1-x)
    (e : 1≤E) (tp : 0<t) (bmax : b≤δ*E^2) (smin : δ≤b*s)
    (lo : x+b*s/E≤1/t) (hi : 1/t≤x+b) : 1/E^2≤t ∧ t≤E := by
  have ep:=zero_lt_one.trans_le e
  have e2 : 1≤E^2 := by nlinarith only [e,sq_nonneg (E-1)]
  have ub : 1/t≤E^2 := by rw [d] at bmax; nlinarith only [hi,bmax,mul_nonneg xn (sub_nonneg.mpr e2)]
  have num : 1≤x*E+b*s := by rw [d] at smin; nlinarith only [smin,mul_nonneg xn (sub_nonneg.mpr e)]
  have lb : 1/E≤1/t := calc
    1/E≤(x*E+b*s)/E := div_le_div_of_nonneg_right num ep.le
    _ = x+b*s/E := by field_simp [ep.ne']
    _ ≤ 1/t := lo
  exact ⟨(div_le_iff₀ (pow_pos ep 2)).mpr (by simpa only [mul_comm] using (div_le_iff₀ tp).mp ub),
    by simpa using (div_le_div_iff₀ ep tp).mp lb⟩

theorem banda_oblicua_desde_el_reciproco {d b u B M : ℝ} (dp : 0<d) (bn : 0≤b) (bB : b≤B)
    (ub : u≤M^2) (rec : 1/d=1+b*u) : 1/(1+B*M^2)≤d := by
  have Bn:=bn.trans bB
  have den : 0<1+B*M^2 := by positivity
  have bu:=(mul_le_mul_of_nonneg_left ub bn).trans (mul_le_mul_of_nonneg_right bB (sq_nonneg M))
  have h : 1/d≤1+B*M^2 := rec.le.trans (add_le_add_left bu 1)
  exact (div_le_iff₀ den).mpr (by simpa only [mul_comm] using (div_le_iff₀ dp).mp h)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.bandas_de_las_medias
#print axioms ArticuloA.Historias.banda_transversal_desde_el_reciproco
#print axioms ArticuloA.Historias.banda_oblicua_desde_el_reciproco
