import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open Filter Real
open scoped Topology

theorem precision_de_las_fibras_respecto_de_los_huecos (s : ℝ) (hs : 0<s) :
    ∀ᶠ n : ℕ in atTop,(n:ℝ)^(-(1/4:ℝ))≤s*fraccionReserva n/100 := by
  let b:=(1/4:ℝ)-4*exponenteReserva
  have bp : 0<b := by norm_num [b,exponenteReserva]
  have tend : Tendsto (fun n : ℕ=>(n:ℝ)^(-b)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop bp).comp tendsto_natCast_atTop_atTop
  have sp : 0<s/1600000 := by positivity
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1,tend.eventually_lt_const sp] with n cuts n1 hl
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have prod : (n:ℝ)^(-(1/4:ℝ))*(n:ℝ)^(4*exponenteReserva)=(n:ℝ)^(-b) := by
    rw [←Real.rpow_add np]; congr 1; dsimp [b]; ring
  have low:=cuts.2.2.1
  have eq : (n:ℝ)^(-(1/4:ℝ)) ≤ (s/1600000)/(n:ℝ)^(4*exponenteReserva) := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos np _),prod]
    exact hl.le
  have mul:=mul_le_mul_of_nonneg_left low hs.le
  apply eq.trans
  calc
    _ = s*((1/16000:ℝ)/(n:ℝ)^(4*exponenteReserva))/100 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right mul (by norm_num)

theorem tasa_de_reserva_inferior_a_la_holgura_absoluta (L : ℝ) (hl : 0<L) :
    ∀ᶠ n : ℕ in atTop,(n:ℝ)^(-exponenteReserva)≤L/8 := by
  have tend : Tendsto (fun n : ℕ=>(n:ℝ)^(-exponenteReserva)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num [exponenteReserva])).comp tendsto_natCast_atTop_atTop
  filter_upwards [tend.eventually_lt_const (show 0<L/8 by positivity)] with n hn
  exact hn.le

end ArticuloA.Historias
#print axioms ArticuloA.Historias.precision_de_las_fibras_respecto_de_los_huecos
#print axioms ArticuloA.Historias.tasa_de_reserva_inferior_a_la_holgura_absoluta
