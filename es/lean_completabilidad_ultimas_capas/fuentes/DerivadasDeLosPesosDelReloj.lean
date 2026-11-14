import AdjuntoPonderadoDeLosDieciseisPatrones
open scoped NNReal
namespace ArticuloA.Historias
noncomputable section

/-- First difference and error of the linear part for one normalized clock step. -/
structure PasoDelReloj (x v x' d B : ℝ) : Prop where
  old : |x|≤B
  new : |x'|≤B
  slope : |v|≤B
  change : |x'-x|≤B*d
  error : |x'-x-d*v|≤B*d^2

theorem paso_constante_igual_a_uno {d : ℝ} (dp : 0≤d) : PasoDelReloj 1 0 1 d 1 := by
  constructor <;> simp [dp,sq_nonneg]

theorem paso_del_numerador {y d : ℝ} (dp : 0≤d) (dy : d≤y) (one : y≤1) :
    PasoDelReloj y (-1) (y-d) d 1 := by
  have yp:=dp.trans dy
  constructor
  · simpa [abs_of_nonneg yp] using one
  · rw [abs_of_nonneg (sub_nonneg.mpr dy)]; linarith
  · norm_num
  · simp [sub_sub_cancel_left,abs_of_nonneg dp]
  · simp [sq_nonneg]

theorem paso_del_reciproco {z d ζ : ℝ} (dp : 0≤d) (zp : 0<ζ) (cut : ζ≤z-d) :
    let U:=max 1 ζ⁻¹
    PasoDelReloj z⁻¹ (z⁻¹^2) (z-d)⁻¹ d (U^3) := by
  intro U
  have zp' : 0<z-d := zp.trans_le cut
  have zp0 : 0<z := by linarith
  have h1 : 1≤U := le_max_left _ _
  have ub : 0≤U := zero_le_one.trans h1
  have s : z⁻¹≤U := (inv_anti₀ zp (by linarith : ζ≤z)).trans (le_max_right _ _)
  have t : (z-d)⁻¹≤U := (inv_anti₀ zp cut).trans (le_max_right _ _)
  have u2 : U≤U^2 := by nlinarith [mul_nonneg ub (sub_nonneg.mpr h1)]
  have u3 : U^2≤U^3 := by nlinarith [mul_nonneg (sq_nonneg U) (sub_nonneg.mpr h1)]
  have sp:=inv_nonneg.mpr zp0.le
  have tp:=inv_nonneg.mpr zp'.le
  have delta : (z-d)⁻¹-z⁻¹=z⁻¹*(z-d)⁻¹*d := by field_simp; ring; simp
  have rem : (z-d)⁻¹-z⁻¹-d*z⁻¹^2=z⁻¹^2*(z-d)⁻¹*d^2 := by field_simp; ring
  have pair:=mul_le_mul s t tp ub
  have sqb:=pow_le_pow_left₀ sp s 2
  constructor
  · exact (abs_of_nonneg sp).le.trans (s.trans (u2.trans u3))
  · exact (abs_of_nonneg tp).le.trans (t.trans (u2.trans u3))
  · exact (abs_of_nonneg (sq_nonneg _)).le.trans (sqb.trans u3)
  · rw [delta,abs_of_nonneg (mul_nonneg (mul_nonneg sp tp) dp)]
    exact mul_le_mul_of_nonneg_right ((by simpa [sq] using pair : z⁻¹*(z-d)⁻¹≤U^2).trans u3) dp
  · rw [rem,abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) tp) (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [pow_succ U 2] using mul_le_mul sqb t tp (sq_nonneg U)

theorem producto_de_pasos {x v x' y w y' d A B : ℝ} (dp : 0≤d) (h : PasoDelReloj x v x' d A)
    (k : PasoDelReloj y w y' d B) : PasoDelReloj (x*y) (v*y+x*w) (x'*y') d (3*A*B) := by
  have ap := (abs_nonneg _).trans h.old
  have bp := (abs_nonneg _).trans k.old
  have ab:=mul_nonneg ap bp
  have bound {u v' E F : ℝ} (p : |u|≤E) (q : |v'|≤F) : |u*v'|≤E*F := by
    rw [abs_mul]; exact mul_le_mul p q (abs_nonneg _) ((abs_nonneg _).trans p)
  constructor
  · exact (bound h.old k.old).trans (by linarith)
  · exact (bound h.new k.new).trans (by linarith)
  · exact (abs_add_le _ _).trans ((add_le_add (bound h.slope k.old) (bound h.old k.slope)).trans (by linarith))
  · rw [show x'*y'-x*y=(x'-x)*y'+x*(y'-y) by ring]
    apply (abs_add_le _ _).trans
    exact (add_le_add (bound h.change k.new) (bound h.old k.change)).trans (by nlinarith [mul_nonneg ab dp])
  · rw [show x'*y'-x*y-d*(v*y+x*w)=(x'-x-d*v)*y+x*(y'-y-d*w)+(x'-x)*(y'-y) by ring]
    apply (abs_add_le _ _).trans
    apply (add_le_add_right (abs_add_le _ _) _).trans
    exact (add_le_add (add_le_add (bound h.error k.old) (bound h.old k.error))
      (bound h.change k.change)).trans_eq (by ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.paso_del_reciproco
#print axioms ArticuloA.Historias.producto_de_pasos
