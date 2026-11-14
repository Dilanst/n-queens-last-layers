import CampoLogaritmicoDeLaDensidadDiscreta
import EntropiaDeLasLineasEnIndicesDeCuadratura
import PerdidaDeEntropiaDeUnaDensidadReservada
namespace ArticuloA.Historias
open Perfil Repair Real
open scoped BigOperators NNReal
noncomputable section

theorem identidad_de_entropia_para_la_muestra {n h q : ℕ} {p κ M L} (hn : 0<n) (hq : 0<q)
    (x : ℝ≥0) (eqx : x=fraccionHuecos n h) (xp : 0<(x:ℝ)) (kp : 0<κ)
    (sp : ControlEspacial p κ M L) :
    let U:=holguraInicial n h p
    let V:=fun i j=>1-cargaLinea n q p i j
    entropiaDiscretaDeReserva (cargaCelda n q p)=
      (q:ℝ)*(log ((x:ℝ)^2*Wfisico n p)-log q)-3*q-
      (∑ i,∑ j : Indice n,log (U i j))-
      (∑ i,∑ j : Indice n,V i j*(log (V i j)-log (U i j))) := by
  intro U V
  have pt (i : Fin 4) (j : Indice n) :
      aporteCelda (V i j)-cargaLinea n q p i j*log (U i j) =
        -log (U i j)-V i j*(log (V i j)-log (U i j)) := by
    unfold aporteCelda
    dsimp only [V]
    ring
  have sum:=congrArg (fun f : Fin 4→Indice n→ℝ=> ∑ i,∑ j,f i j) (funext fun i=>funext (pt i))
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib] at sum
  rw [entropiaDiscretaDeReserva,entropia_de_celdas_en_el_campo hn hq x eqx xp kp sp,
    entropia_de_lineas_en_cuadratura,(masa_y_signo_de_la_densidad_fisica (q:=q) hn sp kp).1]
  dsimp only [U,V] at sum ⊢
  linarith only [sum]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.identidad_de_entropia_para_la_muestra
