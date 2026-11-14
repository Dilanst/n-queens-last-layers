import EntropiaDeLasHolgurasDeLinea
namespace ArticuloA.Historias
open Repair Limites Real
open scoped BigOperators
noncomputable section
open Classical

/-- Discrete entropy. The four labels without squares contribute zero. -/
def entropiaDiscretaDeReserva {n} (w : Cell n→ℝ) :=
  entropiaCeldas w+entropiaLineas w-3*(∑ e : Cell n,w e)

theorem entropia_de_reserva_con_perdida_explicita {n : ℕ} (np : 0<(n:ℝ))
    (w : Cell n→ℝ) (u : LineaReservable n→Bool) (q X η : ℝ)
    (pos : ∀ e,0≤w e) (cap : ∀ e,w e≤1)
    (mass : (∑ e : Cell n,w e)=q) (ret : (∑ e : Cell n,pesoRetenido w u e)=X)
    (xp : 0<X) (loss : X≤q) (two : q/X≤2) (hp : 0<η)
    (orig : ∀ i,1-masaBajo w (enLaFibra i)∈Set.Icc η 1)
    (after : ∀ i,1-masaBajo (fun e=>(q/X)*pesoRetenido w u e) (enLaFibra i)∈Set.Icc η 1) :
    entropiaDiscretaDeReserva w-entropiaDiscretaDeReserva (fun e=>(q/X)*pesoRetenido w u e) ≤
      (q-X)*(2*log n+2+8*(1+|log η|))+1 := by
  let v:=fun e=>(q/X)*pesoRetenido w u e
  have cv : entropiaCeldas w-entropiaCeldas v≤2*(q-X)*log n+1+2*(q-X) :=
    perdida_de_entropia_en_las_celdas np w u q X pos cap mass ret xp loss two
  have line:=costo_de_lineas_en_la_reserva w v η hp orig after
  have diff : (∑ e : Cell n,|v e-w e|)=2*(q-X) :=
    variacion_total_despues_de_normalizar w u q X pos mass ret xp loss
  rw [diff] at line
  have mv : (∑ e : Cell n,v e)=q := by
    dsimp [v]; rw [←Finset.mul_sum,ret,div_mul_cancel₀ _ xp.ne']
  change entropiaDiscretaDeReserva w-entropiaDiscretaDeReserva v≤_
  simp only [entropiaDiscretaDeReserva,mass,mv]
  linarith only [cv,(abs_le.mp line).1]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_reserva_con_perdida_explicita
