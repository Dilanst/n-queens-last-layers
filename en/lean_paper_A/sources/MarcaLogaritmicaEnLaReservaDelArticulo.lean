import EntropiaDeLaCasillaDesdeLaMarcaSeguida
import ColaDelPrefijoConLaMarcaDeEntropia
import EscalaDeLaProbabilidadDeFalloFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Filter
open scoped Topology
def pruebasDeEntropia {n} (v : Cell n→ℝ≥0) (i : Bool) (e : Cell n) : ℝ :=
  if i then marcaLogaritmica ((n:ℝ)^2) (v e)/(2*log n) else 1

theorem la_marca_del_logaritmo_esta_normalizada {n} (v : Cell n→ℝ≥0) (np : 1<(n:ℝ))
    (cap : ∀ e,(v e:ℝ)≤1) :
    (∀ i e,0≤pruebasDeEntropia v i e ∧ pruebasDeEntropia v i e≤1) ∧
    ∀ e,marcaLogaritmica ((n:ℝ)^2) (v e)=(2*log n)*pruebasDeEntropia v true e := by
  have ln:=Real.log_pos np
  have lp : 0<2*log n:=by positivity
  constructor
  · intro i e
    cases i with
    | false=>simp [pruebasDeEntropia]
    | true=>
      simp only [pruebasDeEntropia,if_true]
      have hi : max 1 ((n:ℝ)^2*(v e:ℝ))≤(n:ℝ)^2:=max_le (by nlinarith) (mul_le_of_le_one_right (sq_nonneg _) (cap e))
      have lo : 1≤max 1 ((n:ℝ)^2*(v e:ℝ)):=le_max_left _ _
      have b:=Real.log_le_log (lt_of_lt_of_le zero_lt_one lo) hi
      rw [Real.log_pow] at b
      exact ⟨div_nonneg (Real.log_nonneg lo) lp.le,(div_le_one lp).mpr (by simpa only [Nat.cast_ofNat,marcaLogaritmica] using b)⟩
  · intro e; simp only [pruebasDeEntropia,if_true]; field_simp

theorem cola_del_logaritmo_en_la_escala_de_la_reserva :
    ∀ᶠ n : ℕ in atTop, let q:=n-huecosReserva n
      (Fintype.card (IndiceDeSeguimiento n Bool):ℝ)*(q+1)*(2*exp (-(log (n:ℝ))^2))≤25/(n:ℝ)^2 := by
  filter_upwards [fallo_del_seguimiento_a_escala_inversa,eventually_ge_atTop 1] with n bound one
  intro q
  let d:=Real.toNNReal (100*fraccionReserva n)
  have card : (Fintype.card (IndiceDeSeguimiento n Bool):ℝ)≤(Fintype.card (IndiceDeSeguimiento n (Option (Cell n))):ℝ):=by
    simp [IndiceDeSeguimiento,Cell,Fintype.card_option,Fintype.card_sum,Fintype.card_prod]
    have lb : (1:ℝ)≤n:=by exact_mod_cast one
    nlinarith only [sq_nonneg ((n:ℝ)-1),lb]
  have first:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right card (by positivity : 0≤(q:ℝ)+1))
    (by positivity : 0≤2*exp (-(log (n:ℝ))^2))
  change _+((n:ℝ)^2*exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6))≤_ at bound
  exact first.trans ((le_add_of_nonneg_right (by positivity)).trans bound)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.la_marca_del_logaritmo_esta_normalizada
#print axioms ArticuloA.Historias.cola_del_logaritmo_en_la_escala_de_la_reserva
