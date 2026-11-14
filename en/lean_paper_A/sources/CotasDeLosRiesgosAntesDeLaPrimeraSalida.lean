import IdentificacionDelObservableDeLineaAntesDeLaParada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem riesgos_antes_de_salir {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t≤q)
    (l : List (Cell n)) (reg : total masas (opcionesGuiadas v q t l)≠0)
    {η U : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0≤U)
    (cap : ∀ e,(v e:ℝ)≤U) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (wlo : (9/10:ℝ)*q≤(total masas (opcionesGuiadas v q t l)).val)
    (zmax : ∀ i e,masaObservadaDeLinea v q t l i e≤11/10) :
    (∀ e j,riesgoPrevisto v q t e j≤1/(η*q)) ∧
    (∀ e j,riesgoDeLinea (leyDePieza v q t l) e j≤(5/4)/(η*q)) ∧
    (∀ e,leyDePieza v q t l e≤(U/η^4)/((9/10)*q)) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have hπ (e j):=margen_de_fraccion_viva qp tq v slack h1 e j
  let W:=(total masas (opcionesGuiadas v q t l)).val
  have wp : 0<W:=by exact_mod_cast pos_iff_ne_zero.mpr reg
  constructor
  · intro e j
    apply div_le_div₀ zero_le_one ((slack j e).trans (by linarith only [hp])) (mul_pos hp qr)
    rw [mul_comm η]; exact mul_le_mul_of_nonneg_left (hπ e j) qr.le
  constructor
  · intro e j
    rw [riesgo_de_linea_desde_Z v q t l reg j e (hp.trans_le (hπ e j))]
    have base:=mul_le_mul (hπ e j) wlo (show 0≤(9/10:ℝ)*q by positivity) (hp.trans_le (hπ e j)).le
    calc _ ≤ (11/10)/(η*((9/10)*q)):=div_le_div₀ (by norm_num) (zmax j e) (by positivity) base
         _ ≤ (5/4)/(η*q):=by
           apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
           nlinarith only [mul_pos hp qr]
  · intro e
    rw [probabilidad_de_pieza_como_cociente v q t l reg]
    have w:=peso_acotado_por_las_holguras v Finset.univ e hp (fun j _=>hπ e j) (cap e)
    have top : (pesoGuiado v q t e:ℝ)≤U/η^4:=by
      rw [←cuatro_familias_dan_el_peso_de_G v q t e (fun j=>(hp.trans_le (hπ e j)).le)]
      simpa using w.2
    apply div_le_div₀ (by positivity) _ (by positivity) wlo
    unfold masaVivaEn
    split
    · exact top
    · positivity

theorem linea_ocupada_tiene_masa_observada_cero {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (i : Fin 4) (z : Cell n) (hit : ∃ b∈l,llaveDeLinea i b=llaveDeLinea i z) :
    masaObservadaDeLinea v q t l i z=0 := by
  obtain ⟨b,hb,eq⟩:=hit
  unfold masaObservadaDeLinea
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro e he
  have inc:=(Finset.mem_filter.mp he).2
  have dead : ¬∀ d∈l,compatible e d:=fun free=>(compatible_iff_llaves _ _).mp (free b hb) i (inc.trans eq.symm)
  exact if_neg dead
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.riesgos_antes_de_salir
#print axioms ArticuloA.Historias.linea_ocupada_tiene_masa_observada_cero
