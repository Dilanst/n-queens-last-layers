import B1aConMarcasEnUnaReservaFija
import PerdidaDeEntropiaDeUnaDensidadReservada
import ConstanteDelCostoEntropicoDeB1
namespace ArticuloA.Historias
open Repair Limites Filter Real
open scoped Topology BigOperators
noncomputable section
open Classical

theorem masaBajo_no_negativa {n} (w : Cell n→ℝ) (p : ∀ e,0≤w e) (P : Cell n→Prop) : 0≤masaBajo w P := by
  apply Finset.sum_nonneg
  intro e _
  unfold pesoCuando
  split <;> simp [p]

/-- Admisibilidad, entropía y absorbedores de la reserva, en la escala y con la finalidad de existencia que utiliza el primer orden. -/
theorem B1_con_entropia_y_marcas_para_la_misma_reserva (A s L : ℝ) (ap : 0<A) (sp : 0<s)
    (lp : 0<L) (l1 : L≤1) :
    ∀ᶠ n : ℕ in atTop, ∀ (w : Cell n→ℝ) (q : ℝ), (∀ e,0≤w e) → (∀ e,w e≤A/n) →
      (∑ e : Cell n,w e)=q → 4≤q → q≤n → (n:ℝ)/2≤q →
      (∀ i : Bool × Fin n,masaBajo w (enLaFibra (.inl i))≤1-s*fraccionReserva n/2) →
      (∀ j : LineaReservable n,masaBajo w (enLaFibra (.inr j))≤1-3*L/4) →
      let ε:=fraccionReserva n
      let τ:=(n:ℝ)^(-exponenteReserva)
      ∃ u : LineaReservable n→Bool,
        let X:=∑ e : Cell n,pesoRetenido w u e
        let v:=fun e=>(q/X)*pesoRetenido w u e
        0<X ∧ (∑ e : Cell n,v e)=q ∧ (∀ e,0≤v e ∧ v e≤2*(A/n)) ∧
        (∀ i,masaBajo v (enLaFibra i)≤1-s*ε/4) ∧
        entropiaDiscretaDeReserva w-constanteB1 s*τ*n*log (1/ε)≤entropiaDiscretaDeReserva v ∧
        ∀ z : Cell n,τ^4*q/8≤masaBajo v (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z) := by
  have slim : Tendsto (fun n=>s*fraccionReserva n) atTop (𝓝 0) := by
    simpa using fraccion_de_reserva_tiende_a_cero.const_mul s
  filter_upwards [B1a_y_marcas_para_el_proceso A s L ap sp lp l1,perdida_en_presupuesto_N3A2_7 s sp,
    escalas_del_costo_entropico s sp,slim.eventually_lt_const lp,eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop A] with n choose budget scales slim n1 nA
  intro w q pos cap mass qm qM half rc ob
  obtain ⟨u,xp,one,two,mv,cells,fibers,lost,_,marks⟩:=choose w q pos cap mass qm qM half rc ob
  let X:=∑ e : Cell n,pesoRetenido w u e
  let v:=fun e=>(q/X)*pesoRetenido w u e
  let η:=s*fraccionReserva n/4
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have cap1 (e) : w e≤1 := (cap e).trans ((div_le_one np).mpr nA)
  have loss : X≤q := by
    change 1≤q/X at one
    simpa using (le_div_iff₀ xp).mp one
  have ep : 0<fraccionReserva n := scales.1
  have hp : 0<η := div_pos (mul_pos sp ep) (by norm_num)
  have orig (i) : 1-masaBajo w (enLaFibra i)∈Set.Icc η 1 := by
    refine ⟨?_,sub_le_self _ (masaBajo_no_negativa w pos _)⟩
    unfold η
    rcases i with i|j
    · linarith only [rc i,mul_nonneg sp.le ep.le]
    · linarith only [ob j,slim,lp]
  have new (i) : 1-masaBajo v (enLaFibra i)∈Set.Icc η 1 := by
    refine ⟨?_,sub_le_self _ (masaBajo_no_negativa v (fun e=>(cells e).1) _)⟩
    have fibers_i : masaBajo v (enLaFibra i)≤1-η := fibers i
    linarith only [fibers_i]
  have bound:=entropia_de_reserva_con_perdida_explicita np w u q X η pos cap1 mass rfl xp loss two hp orig new
  have final:=bound.trans (budget (q-X) (sub_nonneg.mpr loss) lost)
  exact ⟨u,xp,mv,cells,fibers,by linarith only [final],marks⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.B1_con_entropia_y_marcas_para_la_misma_reserva
