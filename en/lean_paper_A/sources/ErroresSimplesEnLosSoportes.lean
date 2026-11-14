import ErrorDeCadaLineaInversa
import RestoDeLosDieciseisPatrones
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

/-- A dormant source selects its four active lines. A physical vacancy
also selects an active pre-hit line, using the promoted support at the target. -/
theorem error_sumado_de_fuente_y_destino {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (hn : 0<n) (leg : Legal X.physical) (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (o v j l : Bool) (i : Fin 4) :
    let D:=constanteUna A.l A.M C*(E+1)
    let source:=fun (first : Bool) (u : Mark n) => lineLabel (if first then u.1 else u.2) i
    let target:=fun (u : Mark n) (i : Fin 4) => lineLabel (corners u).2 i
    (∀ first : Bool,
      (pesoDeUnaFuente n (if first then false else o)*pesoDeUnaFuente n (if first then v else false))*
      masas.sum (soporteDeParejas X (if first then false else o) (if first then v else false) j l)
        (fun u => errorDeLinea A (source first u) true)≤D) ∧
    (pesoDeUnaFuente n o*pesoDeUnaFuente n v)*
      masas.sum (soporteDeParejas X o v true l) (fun u => errorDeLinea A (target u 2) j)≤D ∧
    (pesoDeUnaFuente n o*pesoDeUnaFuente n v)*
      masas.sum (soporteDeParejas X o v j true) (fun u => errorDeLinea A (target u 3) l)≤D := by
  intro D source target
  have fromSource (e : Cell n) (av : E2.available X (lines e)=true) :
      activeLine X (lineLabel e i) := ⟨on_board e i,List.all_eq_true.mp av i (by simp [List.finRange,List.mem_ofFn]; omega)⟩
  constructor
  · intro first
    apply cota_de_suma_de_borrados hn X leg
    intro u hu
    have st:=((miembros_del_soporte X u.1 u.2 _ _ j l).mp hu).2
    apply error_de_la_tasa_en_linea_activa A hn E C he ho hb _ _ u.1 true
    cases first
    · exact fromSource u.2 st.2.1
    · exact fromSource u.1 st.1
  constructor
  · apply cota_de_suma_de_borrados hn X leg
    intro u hu
    have st:=((miembros_del_soporte X u.1 u.2 o v true l).mp hu).2
    exact error_de_la_tasa_en_linea_activa A hn E C he ho hb (lineLabel (corners u).2 2) ⟨on_board (corners u).2 2,st.2.2.1⟩ u.1 j
  · apply cota_de_suma_de_borrados hn X leg
    intro u hu
    have st:=((miembros_del_soporte X u.1 u.2 o v j true).mp hu).2
    exact error_de_la_tasa_en_linea_activa A hn E C he ho hb (lineLabel (corners u).2 3) ⟨on_board (corners u).2 3,st.2.2.2⟩ u.1 l

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_sumado_de_fuente_y_destino
