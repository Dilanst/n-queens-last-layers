import CostoSublinealDeLasMarcas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

def exponenteReserva : ℝ:=1/146
def huecosReserva (n : ℕ) : ℕ:=⌊(1/8000:ℝ)*(n:ℝ)^(1-4*exponenteReserva)⌋₊
def fraccionReserva (n : ℕ) : ℝ:=(huecosReserva n:ℝ)/n

theorem cortes_de_la_reserva :
    ∀ᶠ n : ℕ in atTop, 1≤huecosReserva n ∧ huecosReserva n≤n ∧
    (1/16000:ℝ)/(n:ℝ)^(4*exponenteReserva)≤fraccionReserva n ∧
    fraccionReserva n≤(1/8000:ℝ)/(n:ℝ)^(4*exponenteReserva) := by
  have big : Tendsto (fun n : ℕ=>(n:ℝ)^(1-4*exponenteReserva)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [exponenteReserva])).comp tendsto_natCast_atTop_atTop
  filter_upwards [big.eventually_ge_atTop 16000,eventually_ge_atTop 1] with n hn np
  have one : (1:ℝ)≤n:=by exact_mod_cast np
  have pos : 0<(n:ℝ):=by linarith
  let y:=(1/8000:ℝ)*(n:ℝ)^(1-4*exponenteReserva)
  have y2 : 2≤y:=by dsimp [y]; linarith
  have lo:=Nat.lt_floor_add_one y
  have hi:=Nat.floor_le (by linarith : 0≤y)
  have mx : 1≤(n:ℝ)^(4*exponenteReserva):=Real.one_le_rpow one (by norm_num [exponenteReserva])
  have yn : y=(1/8000:ℝ)*((n:ℝ)/(n:ℝ)^(4*exponenteReserva)):=by
    dsimp [y]; rw [Real.rpow_sub pos,Real.rpow_one]
  have yp : y≤n:=by
    rw [yn]
    have div:=div_le_self pos.le mx
    linarith
  have nn : 1≤huecosReserva n:=(Nat.one_le_floor_iff y).mpr (by linarith)
  have mn : huecosReserva n≤n:=by exact_mod_cast hi.trans yp
  refine ⟨nn,mn,?_,?_⟩ <;> unfold fraccionReserva
  · apply (le_div_iff₀ pos).mpr
    change _ ≤ (⌊y⌋₊:ℝ)
    have eq : (1/16000:ℝ)/(n:ℝ)^(4*exponenteReserva)*n=y/2:=by rw [yn]; ring
    rw [eq]; linarith
  · apply (div_le_iff₀ pos).mpr
    change (⌊y⌋₊:ℝ)≤_
    convert hi using 1
    rw [yn]
    ring

theorem fraccion_de_reserva_tiende_a_cero : Tendsto fraccionReserva atTop (𝓝 0) := by
  have small : Tendsto (fun n : ℕ=>(1/8000:ℝ)*(n:ℝ)^(-(4*exponenteReserva))) atTop (𝓝 0):=by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num [exponenteReserva] : 0<4*exponenteReserva)).comp
      tendsto_natCast_atTop_atTop).const_mul (1/8000:ℝ)
  apply squeeze_zero_norm' _ small
  filter_upwards [cortes_de_la_reserva] with n h
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold fraccionReserva; positivity),
    Real.rpow_neg (Nat.cast_nonneg n),←div_eq_mul_inv]
  exact h.2.2.2

theorem perdida_de_marcas_en_la_escala_de_G :
    Tendsto (fun n : ℕ=>4*(huecosReserva n:ℝ)*log n/(n:ℝ)) atTop (𝓝 0) := by
  apply costo_de_marcas_es_sublineal (C:=1/8000) (d:=4*exponenteReserva) (by norm_num [exponenteReserva])
  exact Eventually.of_forall (fun n=>Nat.floor_le (by positivity))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cortes_de_la_reserva
#print axioms ArticuloA.Historias.fraccion_de_reserva_tiende_a_cero
#print axioms ArticuloA.Historias.perdida_de_marcas_en_la_escala_de_G
