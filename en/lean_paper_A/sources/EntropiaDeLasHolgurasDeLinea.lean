import EntropiaDeLasCasillasTrasLaReserva
import VariacionTotalDeLaReservaNormalizada
namespace ArticuloA.Historias
open Repair Limites Real
open scoped BigOperators
noncomputable section
open Classical

theorem oscilacion_del_aporte_con_holgura {x y η : ℝ} (hp : 0<η)
    (hx : x∈Set.Icc η 1) (hy : y∈Set.Icc η 1) :
    |aporteCelda y-aporteCelda x|≤(1+|log η|)*|y-x| := by
  have ordered {a b : ℝ} (lo : η≤a) (ab : a≤b) (hi : b≤1) :
      |aporteCelda b-aporteCelda a|≤(1+|log η|)*|b-a| := by
    have ap := hp.trans_le lo
    have bp := ap.trans_le ab
    have ell := Real.log_le_log (hp.trans_le lo) ab
    have lb := Real.log_le_log hp (lo.trans ab)
    have ly := Real.log_nonpos bp.le hi
    have le := Real.log_le_sub_one_of_pos (div_pos bp ap)
    rw [Real.log_div bp.ne' ap.ne'] at le
    have logdiff : a*(log b-log a)≤b-a := by
      have bnd:=mul_le_mul_of_nonneg_right le ap.le
      simp only [sub_mul,div_mul_cancel₀ b ap.ne',one_mul] at bnd
      linarith only [bnd]
    have bound : |log b|≤|log η| := by
      rw [abs_of_nonpos ly,abs_of_nonpos (Real.log_nonpos hp.le ((lo.trans ab).trans hi))]
      linarith only [lb]
    have id : aporteCelda b-aporteCelda a=-(b-a)*log b-a*(log b-log a) := by unfold aporteCelda; ring
    rw [id]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg ap.le,abs_of_nonneg (sub_nonneg.mpr ell)]
    have bd:=mul_le_mul_of_nonneg_left bound (abs_nonneg (b-a))
    rw [abs_of_nonneg (sub_nonneg.mpr ab)] at bd ⊢
    linarith only [bd,logdiff]
  rcases le_total x y with xy|yx
  · exact ordered hx.1 xy hy.2
  · simpa [abs_sub_comm] using ordered hy.1 yx hx.2

def entropiaLineas {n} (w : Cell n→ℝ) :=
  ∑ i : FibraDeB1 n,aporteCelda (1-masaBajo w (enLaFibra i))

theorem costo_de_lineas_en_la_reserva {n} (w v : Cell n→ℝ) (η : ℝ) (hp : 0<η)
    (orig : ∀ i,1-masaBajo w (enLaFibra i)∈Set.Icc η 1)
    (new : ∀ i,1-masaBajo v (enLaFibra i)∈Set.Icc η 1) :
    |entropiaLineas v-entropiaLineas w|≤(1+|log η|)*(4*∑ e : Cell n,|v e-w e|) := by
  unfold entropiaLineas
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (variacion_agregada_para_la_entropia_de_lineas v w) (by positivity))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have b:=oscilacion_del_aporte_con_holgura hp (orig i) (new i)
  rw [show 1-masaBajo v (enLaFibra i)-(1-masaBajo w (enLaFibra i)) =
    -(masaBajo v (enLaFibra i)-masaBajo w (enLaFibra i)) by ring,abs_neg] at b
  exact b

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscilacion_del_aporte_con_holgura
#print axioms ArticuloA.Historias.costo_de_lineas_en_la_reserva
