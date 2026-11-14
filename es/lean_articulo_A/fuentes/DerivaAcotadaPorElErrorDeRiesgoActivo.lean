import ErrorDeDerivaDeLaLineaCongelada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped BigOperators NNReal
noncomputable section
open Classical

theorem estimar_la_deriva_sobre_casillas_vivas {n} (A : Finset (Cell n)) (s : Finset (Fin 4))
    (l : List (Cell n)) (a : Cell n→ℝ) (u p : Cell n→Fin 4→ℝ)
    {d H R : ℝ} (an : ∀ e∈A,0≤a e)
    (track : ∀ e∈A,(∀ b∈l,compatible e b)→∀ i∈s,|u e i-p e i|≤H)
    (linear : |d-∑ e∈A,masaVivaEn l a e*((∑ i∈s,u e i)-(∑ i∈s,p e i))|≤
      (∑ e∈A,masaVivaEn l a e)*R) :
    |d|≤(∑ e∈A,masaVivaEn l a e)*((s.card:ℝ)*H+R) := by
  let main:=∑ e∈A,masaVivaEn l a e*((∑ i∈s,u e i)-(∑ i∈s,p e i))
  have bnd : |main|≤(∑ e∈A,masaVivaEn l a e)*((s.card:ℝ)*H):=by
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro e he
    by_cases live : ∀ b∈l,compatible e b
    · simp only [masaVivaEn,if_pos live,abs_mul,abs_of_nonneg (an e he)]
      apply mul_le_mul_of_nonneg_left _ (an e he)
      rw [←Finset.sum_sub_distrib]
      exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (track e he live)).trans (by simp))
    · simp only [masaVivaEn,if_neg live,zero_mul,abs_zero,le_refl]
  change |d-main|≤_ at linear
  have tri:=abs_add_le (d-main) main
  rw [sub_add_cancel] at tri
  linarith only [tri,linear,bnd,mul_add (∑ e∈A,masaVivaEn l a e) ((s.card:ℝ)*H) R]

theorem coeficiente_nueve_en_el_seguimiento {W Z q X D R dw dz : ℝ}
    (qp : 0<q) (dp : 0<D) (xn : 0≤X) (rn : 0≤R)
    (wmax : W≤11/10*q) (zmax : Z≤11/10)
    (board : |dw|≤W*(4*(X/((9/10)*D))+R))
    (linea : |dz|≤Z*(3*(X/((9/10)*D))+R)) :
    |dw|/q+|dz|≤9/D*X+(22/10)*R := by
  let H:=X/((9/10)*D)
  have hp : 0≤H:=by dsimp [H]; positivity
  have w:=(board.trans (mul_le_mul_of_nonneg_right wmax (show 0≤4*H+R by positivity)))
  have z:=(linea.trans (mul_le_mul_of_nonneg_right zmax (show 0≤3*H+R by positivity)))
  have wh : |dw|/q≤11/10*(4*H+R):=(div_le_iff₀ qp).mpr (by nlinarith only [w])
  have gain : (11/10)*(4*H+R)+(11/10)*(3*H+R)≤9/D*X+(22/10)*R:=by
    have eq : 9/D*X=(81/10)*H:=by dsimp [H]; field_simp [dp.ne']; ring
    rw [eq]
    linarith only [hp]
  exact (add_le_add wh z).trans gain
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.estimar_la_deriva_sobre_casillas_vivas
#print axioms ArticuloA.Historias.coeficiente_nueve_en_el_seguimiento
