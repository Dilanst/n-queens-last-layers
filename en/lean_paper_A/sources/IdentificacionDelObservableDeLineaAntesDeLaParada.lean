import ElRiesgoDeLaLineaDesdeLasMasasObservadas
import SaltosConLaHolguraFisicaDeLaReserva
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem Z_es_la_suma_de_tres_familias {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n)) (i : Fin 4) (z : Cell n)
    (pos : ∀ e j,0<fraccionVivaG v q t e j) :
    (∑ e∈fibraFisicaG i z,masaVivaEn l (fun b=>pesoDeFamiliasG v q t b (Finset.univ.erase i)) e)=
    masaObservadaDeLinea v q t l i z := by
  unfold masaObservadaDeLinea
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have eq:=(Finset.mem_filter.mp he).2
  have π : fraccionVivaG v q t e i=fraccionVivaG v q t z i:=by simp [fraccionVivaG,masaDeLineaG,eq]
  by_cases live : ∀ d∈l,compatible e d
  · simp only [masaVivaEn,if_pos live,tres_familias_dan_el_peso_de_linea v q t e i (pos e),π]
  · simp only [masaVivaEn,if_neg live,mul_zero]

theorem salto_de_Z_con_holgura {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n)
    {κ η U : ℝ} (kn : 0≤κ) (ks : κ≤1/16) (hp : 0<η) (up : 0≤U)
    (pos : ∀ e j,0<fraccionVivaG v q t e j) (rates : ∀ e j,riesgoPrevisto v q t e j≤κ)
    (cap : ∀ e,(v e:ℝ)≤U) (hs : ∀ e j,η≤fraccionVivaG v q (t+1) e j) (b : Cell n) :
    let s:=(Finset.univ : Finset (Fin 4)).erase i
    let a:=fun t' e=>pesoDeFamiliasG v q t' e s
    let S:=fibraFisicaG i z
    let Y:=fun y=>if fueraDeRaiz i z y then deltaDeMasaEn l S (a t) (a (t+1)) y else 0
    |Y (some (b::l))-media (pasoDeG v q t (some l)) Y|≤masaObservadaDeLinea v q t l i z*(6*κ)+3*(U/η^3) := by
  let s:=(Finset.univ : Finset (Fin 4)).erase i
  let a:=fun t' e=>pesoDeFamiliasG v q t' e s
  have size : s.card=3:=by simp [s,Finset.card_erase_of_mem]
  have bound (e) :=peso_acotado_por_las_holguras v s e hp (fun j _=>hs e j) (cap e)
  obtain ⟨d0,dmax⟩:=ganancia_de_la_linea_con_holguras v qp l i z kn ks pos rates
  rw [Z_es_la_suma_de_tres_familias v l i z pos] at dmax
  exact (salto_centrado_de_la_linea v q t l reg i z (a t) (a (t+1))
     (fun e=>(bound e).1) (fun e=>by simpa only [size] using (bound e).2)
     (by positivity) d0 b).trans (add_le_add_right dmax _)

theorem cota_temporal_del_error_de_riesgo {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t≤q)
    (l : List (Cell n)) (reg : total masas (opcionesGuiadas v q t l)≠0)
    (i : Fin 4) (z : Cell n) {η X : ℝ} (hp : 0<η) (h1 : η≤1)
    (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    (wlo : (9/10:ℝ)*q≤(total masas (opcionesGuiadas v q t l)).val)
    (error : |masaObservadaDeLinea v q t l i z-(masaDeLineaG v i z:ℝ)|+
       |(total masas (opcionesGuiadas v q t l)).val-q|/q≤X) :
    |riesgoDeLinea (leyDePieza v q t l) z i-riesgoPrevisto v q t z i|≤
      X/((9/10)*((q:ℝ)-(1-η)*t)) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have tr : (t:ℝ)≤q:=by exact_mod_cast tq
  let π:=fraccionVivaG v q t z i
  have pos : 0<π:=hp.trans_le (margen_de_fraccion_viva qp tq v slack h1 z i)
  have slim:=slack i z
  have margin:=mul_le_mul_of_nonneg_left slim (Nat.cast_nonneg (α:=ℝ) t)
  have mπ : (q:ℝ)-(1-η)*t≤π*q:=by
    dsimp [π,fraccionVivaG]
    field_simp [qr.ne']
    nlinarith only [margin]
  have dpos : 0<(q:ℝ)-(1-η)*t:=by
    have zt:=mul_le_mul_of_nonneg_left tr (sub_nonneg.mpr h1)
    nlinarith [mul_pos hp qr]
  have den := mul_le_mul_of_nonneg_left wlo pos.le
  apply (error_del_riesgo_observado v qp l reg i z pos (by linarith only [slim,hp])).trans
  have xp : 0≤X:=le_trans (by positivity) error
  apply div_le_div₀ xp error (mul_pos (by norm_num) dpos)
  change _≤π*_
  nlinarith only [den,mπ]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.salto_de_Z_con_holgura
#print axioms ArticuloA.Historias.cota_temporal_del_error_de_riesgo
