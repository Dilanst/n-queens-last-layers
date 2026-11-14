import PrimerOrdenDeLasSalidasConReserva
import ElValorInteriorDominaAlLlenoCercaDelBorde
import ErrorDeEntropiaEnLaEscalaDeReserva
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- The normalized form of the entropy bound for the reserved partial placements.
The budget applies to the good partial placements, before they are completed. -/
theorem articulo_A_desde_N3A2_17 {C : ℝ} (O : (n : ℕ)→Finset (Placement n))
    (good : ∀ᶠ n : ℕ in atTop,(O n).Nonempty ∧
      (∃ D A : ℤ→Prop,∀ p∈O n,SalidaDeReserva (huecosReserva n) D A p) ∧
      ((n-huecosReserva n:ℕ):ℝ)*log n+(n:ℝ)*sSup (valoresCartesianosEnMasa (1-fraccionReserva n))
        -C*((n:ℝ)*errorDeLaReserva n)≤log ((O n).card:ℝ)) : ConclusionDelArticuloA := by
  let r (n : ℕ):=(huecosReserva n:ℝ)*log n+C*((n:ℝ)*errorDeLaReserva n)
  have rr : Tendsto (fun n : ℕ=>r n/(n:ℝ)) atTop (𝓝 0):=by
    have sum : Tendsto (fun n : ℕ=>(4*(huecosReserva n:ℝ)*log n/(n:ℝ))/4+C*errorDeLaReserva n)
        atTop (𝓝 0):=by
      simpa using (perdida_de_marcas_en_la_escala_de_G.div_const 4).add (error_de_reserva_tiende_a_cero.const_mul C)
    apply sum.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have nz : (n:ℝ)≠0:=by exact_mod_cast (show n≠0 by omega)
    dsimp [r]; field_simp; ring
  apply articulo_desde_las_salidas_de_G (C:=1/8000) (d:=4*exponenteReserva) (by norm_num [exponenteReserva])
    huecosReserva O r (Eventually.of_forall (fun _=>Nat.floor_le (by positivity))) rr
  obtain ⟨η,ep,inner⟩:=el_supremo_cartesiano_interior_domina_al_lleno
  filter_upwards [good,cortes_de_la_reserva,fraccion_de_reserva_tiende_a_cero.eventually_lt_const ep,
    eventually_ge_atTop 1] with n g cut close hn
  obtain ⟨ne,res,ent⟩:=g
  have mp : (0:ℝ)<huecosReserva n:=by exact_mod_cast (show 0<huecosReserva n from cut.1)
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have grow:=mul_le_mul_of_nonneg_left (inner _ (div_pos mp np) close.le) np.le
  change (n:ℝ)*sSup valoresCartesianosDeAbsorcion≤(n:ℝ)*sSup (valoresCartesianosEnMasa (1-fraccionReserva n)) at grow
  rw [Nat.cast_sub cut.2.1] at ent
  refine ⟨ne,?_,res⟩
  dsimp only [r]; nlinarith only [ent,grow]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.articulo_A_desde_N3A2_17
