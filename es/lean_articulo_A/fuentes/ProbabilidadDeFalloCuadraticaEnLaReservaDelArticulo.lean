import EscalaDeLaProbabilidadDeFalloFisico
import SalidasFisicasDeLaMismaReservaEntropica
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter Perfil
open scoped Topology

theorem existe_reserva_con_fallo_cuadratico_y_entropia_de_entrada :
    ∃ (κ A C : ℝ),0<κ ∧ 0<A ∧ 0≤C ∧ ∀ᶠ n : ℕ in atTop,
    let m:=huecosReserva n
    let q:=n-m
    let x:=fraccionReserva n
    let τ:=(n:ℝ)^(-exponenteReserva)
    let η:=κ*x/4
    let d:=Real.toNNReal (100*x)
    ∃ (u : LineaReservable n→Bool) (v : Cell n→ℝ≥0),
      let D:=oblicuaMarcada u etiquetaD 2
      let F:=oblicuaMarcada u etiquetaA 3
      (∑ e,(v e:ℝ))=q ∧ (∀ e,(v e:ℝ)≤2*(A/n)) ∧ (∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) ∧
      (∀ e,v e≠0→¬D (llaveDeLinea 2 e) ∧ ¬F (llaveDeLinea 3 e)) ∧
      (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-C-constanteB1 κ*τ*n*log (1/x)≤
        entropiaDiscretaDeReserva (fun e=>(v e:ℝ)) ∧
      colaParaTodasLasMarcas v q η (2*(A/n)) ∧
      falloDelParcialReservado v q m D F d≤25/(n:ℝ)^2 := by
  obtain ⟨κ,A,C,kp,ap,cp,source⟩:=reserva_del_optimo_con_probabilidad_de_parciales_legales
  refine ⟨κ,A,C,kp,ap,cp,?_⟩
  filter_upwards [source,fallo_del_seguimiento_a_escala_inversa] with n src top
  obtain ⟨u,v,mass,cap,slack,support,ent,tail,total⟩:=src
  exact ⟨u,v,mass,cap,slack,support,ent,tail,total.trans top⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existe_reserva_con_fallo_cuadratico_y_entropia_de_entrada
