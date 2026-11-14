import ReservaConFibrasYMarcasSimultaneas
import HolguraAlRitmoDeLosHuecosDeReserva
namespace ArticuloA.Historias
open Repair Limites Filter Real
open scoped Topology BigOperators
noncomputable section
open Classical

theorem pertenencia_a_una_oblicua_reservable {n} (j : LineaReservable n) (e : Cell n) :
    j∈lineasPropias e ↔ enLaFibra (.inr j) e := by
  rcases j with ⟨b,j⟩
  cases b <;> simp [lineasPropias,etiquetaD,etiquetaA,enLaFibra,eq_comm]

/-- La misma densidad normalizada tiene (H), las marcas de G y un número controlado de borrados por líneas. -/
theorem B1a_y_marcas_para_el_proceso (A s L : ℝ) (ap : 0<A) (sp : 0<s) (lp : 0<L) (l1 : L≤1) :
    ∀ᶠ n : ℕ in atTop, ∀ (w : Cell n→ℝ) (q : ℝ), (∀ e,0≤w e) → (∀ e,w e≤A/n) →
      (∑ e : Cell n,w e)=q → 4≤q → q≤n → (n:ℝ)/2≤q →
      (∀ i : Bool × Fin n,masaBajo w (enLaFibra (.inl i))≤1-s*fraccionReserva n/2) →
      (∀ j : LineaReservable n,masaBajo w (enLaFibra (.inr j))≤1-3*L/4) →
      let τ:=(n:ℝ)^(-exponenteReserva)
      let t:=(n:ℝ)^(-(1/4:ℝ))
      ∃ u : LineaReservable n→Bool,
        let X:=∑ e : Cell n,pesoRetenido w u e
        let v:=fun e=>(q/X)*pesoRetenido w u e
        0<X ∧ 1≤q/X ∧ q/X≤2 ∧ (∑ e : Cell n,v e)=q ∧ (∀ e,0≤v e ∧ v e≤2*(A/n)) ∧
        (∀ i,masaBajo v (enLaFibra i)≤1-s*fraccionReserva n/4) ∧ q-X≤(2*τ+t)*n ∧
        numeroDeReservas u≤2*(Fintype.card (LineaReservable n):ℝ)*τ ∧
        ∀ z : Cell n,τ^4*q/8≤masaBajo v (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z) := by
  have small : Tendsto (fun n=>s*fraccionReserva n) atTop (𝓝 0) := by
    simpa using fraccion_de_reserva_tiende_a_cero.const_mul s
  filter_upwards [reserva_con_fibras_y_marcas_en_la_escala_original A ap,
    precision_de_las_fibras_respecto_de_los_huecos s sp,
    tasa_de_reserva_inferior_a_la_holgura_absoluta L lp,small.eventually_lt_const lp,
    eventually_ge_atTop 1] with n choose prec cutoff hs n1
  intro w q pos cap mass qm qM half rc ob
  let τ:=(n:ℝ)^(-exponenteReserva)
  let t:=(n:ℝ)^(-(1/4:ℝ))
  let σ:=s*fraccionReserva n
  have non : 0≤σ := by dsimp [σ,fraccionReserva]; positivity
  have fracNon : 0≤s*fraccionReserva n := non
  have r1 (i : Fin n) : masaBajo w (fun e=>e.1=i)≤1 := (rc (false,i)).trans (by linarith only [fracNon])
  have c1 (i : Fin n) : masaBajo w (fun e=>e.2=i)≤1 := (rc (true,i)).trans (by linarith only [fracNon])
  have d1 (j : LineaReservable n) : masaBajo w (fun e=>j∈lineasPropias e)≤1 := by
    apply (masaBajo_mono w pos (fun e h=>(pertenencia_a_una_oblicua_reservable j e).mp h)).trans
    exact (ob j).trans (by linarith)
  obtain ⟨u,regular,count,marked⟩:=choose w q pos cap r1 c1 d1 mass qm qM half
  have a:=admisibilidad_de_la_reserva_fisica w u q τ t σ L (A/n) (by linarith only [qm])
    (by linarith only [half]) qM mass (by dsimp [τ]; positivity) cutoff non hs.le l1
    (by dsimp [t]; positivity) prec pos cap rc ob regular
  rcases a with ⟨xp,one,two,total,cells,fibers,lost⟩
  refine ⟨u,xp,one,two,total,cells,fibers,lost,count,fun z=>?_⟩
  have h:=marked _ one z
  apply h.trans
  apply Finset.sum_le_sum
  intro e _
  unfold pesoCuando pesoRetenido
  by_cases yes : quedaTrasReserva u e <;> simp [yes]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.B1a_y_marcas_para_el_proceso
