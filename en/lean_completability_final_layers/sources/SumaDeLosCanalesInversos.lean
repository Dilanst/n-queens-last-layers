import ErroresSimplesEnLosSoportes
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

/-- Sum of absolute single-line and birth rate errors with the scale of the
target pattern. Each term is evaluated on the physical support of its precondition. -/
def costoDeUnPatron {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (o v j l : Bool) : ℝ≥0 :=
  let agg (a b j' l' : Bool) (err : Mark n→ℝ≥0) :=
    (pesoDeUnaFuente n o*pesoDeUnaFuente n v)*masas.sum (soporteDeParejas X a b j' l') err
  (∑ i : Fin 4,if o then 0 else agg o v j l (fun u => errorDeLinea A (lineLabel u.1 i) true))+
  (∑ i : Fin 4,if v then 0 else agg o v j l (fun u => errorDeLinea A (lineLabel u.2 i) true))+
  agg o v true l (fun u => errorDeLinea A (lineLabel (corners u).2 2) j)+
  agg o v j true (fun u => errorDeLinea A (lineLabel (corners u).2 3) l)+
  (if o then agg false v j l (fun u => errorDelAtomo A u.1) else 0)+
  (if v then agg o false j l (fun u => errorDelAtomo A u.2) else 0)

theorem presupuesto_de_los_canales {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (hn : 0<n) (leg : Legal X.physical) (E C : ℝ≥0)
    (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C) :
    ∑ t : CuatroMarcas,costoDeUnPatron A t.1 t.2.1 t.2.2.1 t.2.2.2 ≤
      192*(constanteUna A.l A.M C*(E+1)) := by
  let D:=constanteUna A.l A.M C*(E+1)
  have one (o v j l : Bool) : costoDeUnPatron A o v j l ≤ 12*D := by
    let agg (a b j' l' : Bool) (err : Mark n→ℝ≥0) :=
      (pesoDeUnaFuente n o*pesoDeUnaFuente n v)*masas.sum (soporteDeParejas X a b j' l') err
    have rate (i : Fin 4) := error_sumado_de_fuente_y_destino A hn leg E C he ho hb o v j l i
    have se (i : Fin 4) : (if o then 0 else agg o v j l (fun u => errorDeLinea A (lineLabel u.1 i) true))≤D := by
      cases o
      · exact (rate i).1 true
      · exact zero_le _
    have sf (i : Fin 4) : (if v then 0 else agg o v j l (fun u => errorDeLinea A (lineLabel u.2 i) true))≤D := by
      cases v
      · exact (rate i).1 false
      · exact zero_le _
    have birth (first other) := errores_de_ambos_nacimientos_en_el_soporte A hn leg E C he ho hb first other j l
    have be : (if o then agg false v j l (fun u => errorDelAtomo A u.1) else 0)≤D := by
      cases o
      · exact zero_le _
      · simpa [agg,pesoDeUnaFuente] using birth true v
    have bf : (if v then agg o false j l (fun u => errorDelAtomo A u.2) else 0)≤D := by
      cases v
      · exact zero_le _
      · simpa [agg,pesoDeUnaFuente] using birth false o
    have bound:=add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => se i)) (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => sf i)))
      (rate 0).2.1) (rate 0).2.2) be) bf
    apply bound.trans
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change 4*D+4*D+D+D+D+D≤12*D
    exact le_of_eq (by ring)
  apply (Finset.sum_le_sum (fun t _ => one t.1 t.2.1 t.2.2.1 t.2.2.2)).trans
  have cnt : Fintype.card CuatroMarcas=16 := by decide
  simp only [Finset.sum_const,Finset.card_univ,cnt,nsmul_eq_mul,Nat.cast_ofNat]
  dsimp only [D]; exact le_of_eq (by ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.presupuesto_de_los_canales
