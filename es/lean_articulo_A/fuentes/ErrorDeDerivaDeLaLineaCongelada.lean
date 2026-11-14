import ErrorDeDerivaParaLasCuatroLineas
import CasillasQuePuedeEliminarUnaPieza
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

-- La linealidad de la media para una suma finita viene de MediaDeUnaSumaDeMarcas.

def cambioEnLaLinea {n} (l : List (Cell n)) (i : Fin 4) (z : Cell n)
    (a a' : Cell n→ℝ) (e : Cell n) (y : EstadoGuiado n) : ℝ :=
  if fueraDeRaiz i z y then (match y with | some s=>masaVivaEn s a' e | none=>0)-masaVivaEn l a e else 0

theorem error_de_la_linea_congelada {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n)
    {κ pmax : ℝ} (kn : 0≤κ) (ks : κ≤1/16)
    (pos : ∀ e j,0<fraccionVivaG v q t e j)
    (uref : ∀ e j,riesgoPrevisto v q t e j≤κ)
    (load : ∀ e j,riesgoDeLinea (leyDePieza v q t l) e j≤κ)
    (top : ∀ e,leyDePieza v q t l e≤pmax) :
    let s:=(Finset.univ : Finset (Fin 4)).erase i
    let a:=fun t' e=>pesoDeFamiliasG v q t' e s
    let p:=leyDePieza v q t l
    let Z:=∑ e∈fibraFisicaG i z,masaVivaEn l (a t) e
    |media (pasoDeG v q t (some l)) (fun y=>∑ e∈fibraFisicaG i z,cambioEnLaLinea l i z (a t) (a (t+1)) e y)-
      ∑ e∈fibraFisicaG i z,masaVivaEn l (a t) e*((∑ j∈s,riesgoPrevisto v q t e j)-
        (∑ j∈s,riesgoDeLinea p e j))|≤Z*(100*κ^2+6*pmax) := by
  let s:=(Finset.univ : Finset (Fin 4)).erase i
  let a:=fun t' e=>pesoDeFamiliasG v q t' e s
  let p:=leyDePieza v q t l
  dsimp only
  rw [media_de_suma_finita,←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  have inc:= (Finset.mem_filter.mp he).2
  rw [show media (pasoDeG v q t (some l)) (cambioEnLaLinea l i z (a t) (a (t+1)) e)=_
    from deriva_fisica_de_una_linea_congelada v q t l reg i z e inc _ _]
  by_cases live : ∀ d∈l,compatible e d
  · simp only [masaVivaEn,if_pos live]
    have group : (∑ j∈s,riesgoDeLinea p e j)+riesgoDeLinea p e i=∑ j,riesgoDeLinea p e j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    let U:=∑ j∈s,riesgoPrevisto v q t e j
    let T:=∑ j,riesgoDeLinea p e j
    let D:=∑ j∈s,riesgoDeLinea p e j
    have norm : a (t+1) e*(1-T+3*p e)-a t e*(1-riesgoDeLinea p e i)-a t e*(U-D)=
        a (t+1) e*(1-T+3*p e)-a t e-a t e*(U-T):=by
      change D+riesgoDeLinea p e i=T at group
      rw [←group]; ring
    change |a (t+1) e*(1-T+3*p e)-a t e*(1-riesgoDeLinea p e i)-a t e*(U-D)|≤_
    rw [norm]
    apply (resto_multiplicativo_de_G v qp e s p kn ks (pos e) (uref e) (load e)
      (ley_de_pieza_no_negativa v q t l)).trans
    apply mul_le_mul_of_nonneg_left (by linarith [top e])
    exact div_nonneg (NNReal.coe_nonneg _) (Finset.prod_nonneg (fun j _=>(pos e j).le))
  · simp only [masaVivaEn,if_neg live,zero_mul,sub_self,abs_zero,le_refl]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_la_linea_congelada
