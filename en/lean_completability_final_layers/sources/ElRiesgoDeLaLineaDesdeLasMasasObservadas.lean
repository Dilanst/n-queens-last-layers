import LaLeyDePiezaUsaElNormalizadorDeG
import CasillasQuePuedeEliminarUnaPieza
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

def masaObservadaDeLinea {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (i : Fin 4) (z : Cell n) : ℝ :=
  fraccionVivaG v q t z i*∑ e∈fibraFisicaG i z,masaVivaEn l (fun b=>(pesoGuiado v q t b:ℝ)) e

theorem riesgo_de_linea_desde_Z {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n)
    (pos : 0<fraccionVivaG v q t z i) :
    riesgoDeLinea (leyDePieza v q t l) z i=
       masaObservadaDeLinea v q t l i z/
        (fraccionVivaG v q t z i*(total masas (opcionesGuiadas v q t l)).val) := by
  unfold riesgoDeLinea masaObservadaDeLinea
  rw [←Finset.sum_filter,←div_div, mul_div_cancel_left₀ _ pos.ne']
  simp_rw [probabilidad_de_pieza_como_cociente v q t l reg]
  rw [Finset.sum_div]; rfl

theorem error_del_riesgo_observado {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n)
    (pos : 0<fraccionVivaG v q t z i) (ml : (masaDeLineaG v i z:ℝ)≤1) :
    let W:=(total masas (opcionesGuiadas v q t l)).val
    let Z:=masaObservadaDeLinea v q t l i z
    let m:=(masaDeLineaG v i z:ℝ)
    |riesgoDeLinea (leyDePieza v q t l) z i-riesgoPrevisto v q t z i|≤
      (|Z-m|+|W-q|/q)/(fraccionVivaG v q t z i*W) := by
  let W:=(total masas (opcionesGuiadas v q t l)).val
  let Z:=masaObservadaDeLinea v q t l i z
  let m:=(masaDeLineaG v i z:ℝ)
  let π:=fraccionVivaG v q t z i
  have wp : 0<W:=by exact_mod_cast (pos_iff_ne_zero.mpr reg)
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have mn : 0≤m:=NNReal.coe_nonneg _
  rw [riesgo_de_linea_desde_Z _ _ _ _ reg _ _ pos]
  change |Z/(π*W)-m/(q*π)|≤_
  have ident : Z/(π*W)-m/(q*π)=((Z-m)-m*(W-(q:ℝ))/q)/(π*W):=by
    field_simp [pos.ne',wp.ne',qr.ne']; ring
  rw [ident,abs_div,abs_of_pos (mul_pos pos wp)]
  apply div_le_div_of_nonneg_right _ (mul_pos pos wp).le
  apply (abs_sub _ _).trans
  rw [abs_div,abs_mul,abs_of_nonneg mn,abs_of_pos qr]
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ qr.le
  simpa using mul_le_mul_of_nonneg_right ml (abs_nonneg (W-(q:ℝ)))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_del_riesgo_observado
