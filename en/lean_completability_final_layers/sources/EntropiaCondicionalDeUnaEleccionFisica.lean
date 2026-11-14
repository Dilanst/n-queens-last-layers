import LaLeyDePiezaUsaElNormalizadorDeG
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem entropia_de_la_eleccion_fisica {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (pos : ∀ e i,0<fraccionVivaG v q t e i) :
    let p:=leyDePieza v q t l
    let W:=(total masas (opcionesGuiadas v q t l)).val
    (∑ e,-(p e*log (p e)))=log W-(∑ e,p e*log (v e:ℝ))+
      ∑ e,p e*∑ i,log (fraccionVivaG v q t e i) := by
  let p:=leyDePieza v q t l
  let W:=(total masas (opcionesGuiadas v q t l)).val
  have wp : 0<W:=by exact_mod_cast pos_iff_ne_zero.mpr reg
  have norm : ∑ e,p e=1:=ley_de_pieza_normalizada v q t l reg
  have atom (e) : -(p e*log (p e))=
      p e*log W-p e*log (v e:ℝ)+p e*∑ i,log (fraccionVivaG v q t e i):=by
    by_cases zero : p e=0
    · simp [zero]
    · have eq:=probabilidad_de_pieza_como_cociente v q t l reg e
      change p e=masaVivaEn l _ e/W at eq
      have live : ∀ b∈l,compatible e b:=by
        by_contra dead
        simp only [masaVivaEn,if_neg dead,zero_div] at eq; exact zero eq
      simp only [masaVivaEn,if_pos live] at eq
      rw [←cuatro_familias_dan_el_peso_de_G v q t e (fun i=>(pos e i).le)] at eq
      have nz : (v e:ℝ)≠0:=by
        intro z
        apply zero; rw [eq,pesoDeFamiliasG,z,zero_div,zero_div]
      let P:=∏ i,fraccionVivaG v q t e i
      have pp : P≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>(pos e i).ne')
      have leq : log (p e)=log (v e:ℝ)-(∑ i,log (fraccionVivaG v q t e i))-log W:=by
        change p e=(v e:ℝ)/P/W at eq
        rw [eq,Real.log_div (div_ne_zero nz pp) wp.ne',Real.log_div nz pp]
        dsimp only [P]; rw [Real.log_prod Finset.univ _ (fun i _=>(pos e i).ne')]
      rw [leq]; ring
  change (∑ e,-(p e*log (p e)))=_
  simp_rw [atom]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,norm,one_mul]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_la_eleccion_fisica
