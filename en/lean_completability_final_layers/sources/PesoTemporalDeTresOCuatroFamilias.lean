import HolguraTemporalDelPesoDeGTrasFijarLaReserva
import LinealizacionDelMultiplicadorTemporal
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria
open scoped NNReal BigOperators
noncomputable section
open Classical

def fraccionVivaG {n} (v : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n) (i : Fin 4) : ℝ :=
  1-((t:ℝ)/q)*(masaDeLineaG v i e:ℝ)

def riesgoPrevisto {n} (v : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n) (i : Fin 4) : ℝ :=
  (masaDeLineaG v i e:ℝ)/((q:ℝ)*fraccionVivaG v q t e i)

def pesoDeFamiliasG {n} (v : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n) (s : Finset (Fin 4)) : ℝ :=
  (v e:ℝ)/∏ i∈s,fraccionVivaG v q t e i

theorem margen_de_fraccion_viva {n q t} (qp : 0<q) (tq : t≤q)
    (v : Cell n→ℝ≥0) {η : ℝ} (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (hη : η≤1) (e : Cell n) (i : Fin 4) : η≤fraccionVivaG v q t e i := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have rate : 0≤(t:ℝ)/q:=by positivity
  have z : (t:ℝ)/q≤1:=(div_le_one qr).mpr (by exact_mod_cast tq)
  have a:=mul_le_mul_of_nonneg_left (slack i e) rate
  have b:=mul_le_mul_of_nonneg_right z (sub_nonneg.mpr hη)
  unfold fraccionVivaG
  linarith

theorem cuatro_familias_dan_el_peso_de_G {n} (v : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n)
    (live : ∀ i,0≤fraccionVivaG v q t e i) :
    pesoDeFamiliasG v q t e Finset.univ=(pesoGuiado v q t e:ℝ) := by
  have cv (i : Fin 4) : ((1-(t:ℝ≥0)/q*masaDeLineaG v i e:ℝ≥0):ℝ)=fraccionVivaG v q t e i := by
    have u : (t:ℝ≥0)/q*masaDeLineaG v i e≤1:=by
      apply NNReal.coe_le_coe.mp
      push_cast
      exact sub_nonneg.mp (live i)
    rw [NNReal.coe_sub u]; push_cast; rfl
  simp [pesoDeFamiliasG,pesoGuiado,NNReal.coe_prod,cv]

theorem un_paso_del_denominador {n} (v : Cell n→ℝ≥0) {q : ℕ} (qp : 0<q)
    (t : ℕ) (e : Cell n) (i : Fin 4) (pos : 0<fraccionVivaG v q t e i) :
    fraccionVivaG v q (t+1) e i=fraccionVivaG v q t e i*(1-riesgoPrevisto v q t e i) := by
  have qr : (q:ℝ)≠0:=by exact_mod_cast qp.ne'
  have base : fraccionVivaG v q (t+1) e i=fraccionVivaG v q t e i-(masaDeLineaG v i e:ℝ)/q:=by
    simp only [fraccionVivaG,Nat.cast_add,Nat.cast_one]; ring
  rw [base]
  unfold riesgoPrevisto
  field_simp [qr,pos.ne']; ring

theorem actualizacion_del_peso {n} (v : Cell n→ℝ≥0) {q : ℕ} (qp : 0<q)
    (t : ℕ) (e : Cell n) (s : Finset (Fin 4)) (pos : ∀ i∈s,0<fraccionVivaG v q t e i) :
    pesoDeFamiliasG v q (t+1) e s=pesoDeFamiliasG v q t e s*
       (∏ i∈s,(1-riesgoPrevisto v q t e i))⁻¹ := by
  unfold pesoDeFamiliasG
  rw [Finset.prod_congr rfl (fun i hi=>un_paso_del_denominador v qp t e i (pos i hi)),
    Finset.prod_mul_distrib]
  simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem tres_familias_dan_el_peso_de_linea {n} (v : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n)
    (i : Fin 4) (pos : ∀ j,0<fraccionVivaG v q t e j) :
    pesoDeFamiliasG v q t e (Finset.univ.erase i)=fraccionVivaG v q t e i*(pesoGuiado v q t e:ℝ) := by
  rw [←cuatro_familias_dan_el_peso_de_G v q t e (fun j=>(pos j).le)]
  unfold pesoDeFamiliasG
  rw [←Finset.mul_prod_erase Finset.univ (fraccionVivaG v q t e) (Finset.mem_univ i)]
  field_simp [(pos i).ne',Finset.prod_ne_zero_iff.mpr (fun j _=>(pos j).ne')]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.actualizacion_del_peso
#print axioms ArticuloA.Historias.tres_familias_dan_el_peso_de_linea
