import DerivaAcotadaPorElErrorDeRiesgoActivo
import IdentificacionDelObservableDeLineaAntesDeLaParada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem deriva_del_tablero_antes_de_salir {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (f : Cell n→ℝ) (fn : ∀ e,0≤f e)
    {κ pmax H : ℝ} (kn : 0≤κ) (ks : κ≤1/16) (pos : ∀ e i,0<fraccionVivaG v q t e i)
    (uref : ∀ e i,riesgoPrevisto v q t e i≤κ) (load : ∀ e i,riesgoDeLinea (leyDePieza v q t l) e i≤κ)
    (top : ∀ e,leyDePieza v q t l e≤pmax)
    (track : ∀ e,(∀ b∈l,compatible e b)→∀ i,|riesgoPrevisto v q t e i-riesgoDeLinea (leyDePieza v q t l) e i|≤H) :
    let a:=fun s e=>pesoDeFamiliasG v q s e Finset.univ*f e
    let V:=pesoObservable (a t) (some l)
    |media (pasoDeG v q t (some l)) (deltaDeMasaEn l Finset.univ (a t) (a (t+1)))|≤
      V*(4*H+(100*κ^2+6*pmax)) := by
  let a:=fun s e=>pesoDeFamiliasG v q s e Finset.univ*f e
  let P:=pasoDeG v q t (some l)
  have one:=(deriva_y_error_del_observable v qp l reg f fn kn ks pos uref load top)
  have non (e) : 0≤a t e:=mul_nonneg (div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun i _=>(pos e i).le))) (fn e)
  have cap:=estimar_la_deriva_sobre_casillas_vivas Finset.univ Finset.univ l (a t)
    (riesgoPrevisto v q t) (riesgoDeLinea (leyDePieza v q t l)) (fun e _=>non e) (fun e _ h i _=>track e h i) one
  have eq : media P (deltaDeMasaEn l Finset.univ (a t) (a (t+1)))=
      media P (fun y=>pesoObservable (a (t+1)) y-pesoObservable (a t) (some l)):=by
    dsimp only [P]
    rw [media_del_paso_fisico v q t l reg,media_del_paso_fisico v q t l reg]
    apply Finset.sum_congr rfl; intro b _
    simp only [deltaDeMasaEn,pesoObservable,Finset.sum_sub_distrib]
  dsimp only
  rw [eq]
  simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using cap

theorem deriva_de_Z_antes_de_salir {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n)
    {κ pmax H : ℝ} (kn : 0≤κ) (ks : κ≤1/16) (pos : ∀ e j,0<fraccionVivaG v q t e j)
    (uref : ∀ e j,riesgoPrevisto v q t e j≤κ) (load : ∀ e j,riesgoDeLinea (leyDePieza v q t l) e j≤κ)
    (top : ∀ e,leyDePieza v q t l e≤pmax)
    (track : ∀ e,(∀ b∈l,compatible e b)→∀ j,|riesgoPrevisto v q t e j-riesgoDeLinea (leyDePieza v q t l) e j|≤H) :
    let s:=(Finset.univ : Finset (Fin 4)).erase i
    let a:=fun t' e=>pesoDeFamiliasG v q t' e s
    let S:=fibraFisicaG i z
    let Y:=fun y=>if fueraDeRaiz i z y then deltaDeMasaEn l S (a t) (a (t+1)) y else 0
    |media (pasoDeG v q t (some l)) Y|≤masaObservadaDeLinea v q t l i z*(3*H+(100*κ^2+6*pmax)) := by
  let s:=(Finset.univ : Finset (Fin 4)).erase i
  let S:=fibraFisicaG i z
  let a:=fun t' e=>pesoDeFamiliasG v q t' e s
  let P:=pasoDeG v q t (some l)
  let Y:=fun y=>if fueraDeRaiz i z y then deltaDeMasaEn l S (a t) (a (t+1)) y else 0
  have one:=error_de_la_linea_congelada v qp l reg i z kn ks pos uref load top
  have non (e) : 0≤a t e:=div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun j _=>(pos e j).le))
  have cap:=estimar_la_deriva_sobre_casillas_vivas S s l (a t)
    (riesgoPrevisto v q t) (riesgoDeLinea (leyDePieza v q t l)) (fun e _=>non e) (fun e _ h j _=>track e h j) one
  have eq : media P Y=media P (fun y=>∑ e∈S,cambioEnLaLinea l i z (a t) (a (t+1)) e y):=by
    dsimp only [P]
    rw [media_del_paso_fisico v q t l reg,media_del_paso_fisico v q t l reg]
    apply Finset.sum_congr rfl; intro b _
    by_cases yes : llaveDeLinea i b=llaveDeLinea i z <;> simp [Y,cambioEnLaLinea,fueraDeRaiz,deltaDeMasaEn,yes]
  have card : s.card=3:=by simp [s,Finset.card_erase_of_mem]
  change |media P Y|≤_
  rw [eq,←Z_es_la_suma_de_tres_familias v l i z pos]
  simpa only [card,Nat.cast_ofNat] using cap
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_del_tablero_antes_de_salir
#print axioms ArticuloA.Historias.deriva_de_Z_antes_de_salir
