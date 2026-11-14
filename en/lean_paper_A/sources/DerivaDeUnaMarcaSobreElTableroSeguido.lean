import DerivaConjuntaDeUnPadreFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem deriva_de_una_marca_tras_seguimiento {I : Type} {n q t : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q)
    (tq : t<q) (l : List (Cell n)) (f : I→Cell n→ℝ) (j : I) (fn : ∀ e,0≤f j e) (ft : ∀ e,f j e≤1)
    {η U E : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0≤U) (cap : ∀ e,(v e:ℝ)≤U)
    (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η) (sm : (5/4)/(η*q)≤1/16)
    (small : E≤1/10) (err : sigueTableroYLineas v q t l E) :
    |derivaFisica v q f (.inl j) t (some l)|≤(11/10:ℝ)*q*(4*(E/((9/10)*η*q))+restoDePadre q η U) := by
  let H:=E/((9/10)*η*q)
  let κ:=(5/4)/(η*q)
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have En : 0≤E:=(by positivity : 0≤|tableroG v q t l-q|/(q:ℝ)).trans err.1
  have hn : 0≤H:=by dsimp [H]; positivity
  have kn : 0≤κ:=by dsimp [κ]; positivity
  have rn : 0≤restoDePadre q η U:=by unfold restoDePadre; positivity
  obtain ⟨_,low,top⟩:=regularidad_del_padre_fisico v qp tq l hp.le small slack err
  have reg : total masas (opcionesGuiadas v q t l)≠0:=by
    intro no; rw [no] at low; change (9/10:ℝ)*q≤0 at low; linarith
  have pos e i:=hp.trans_le (margen_de_fraccion_viva qp tq.le v slack h1 e i)
  obtain ⟨ref,load,cell⟩:=riesgos_antes_de_salir v qp tq.le l reg hp h1 up cap slack low top
  have ref' e i : riesgoPrevisto v q t e i≤κ:=(ref e i).trans
    (div_le_div_of_nonneg_right (by norm_num) (mul_nonneg hp.le qr.le))
  have track e (live : ∀ a∈l,compatible e a) i :
      |riesgoPrevisto v q t e i-riesgoDeLinea (leyDePieza v q t l) e i|≤H:=by
    rw [abs_sub_comm]
    have h:=err.2 i e (fun a ha eq=>(compatible_iff_llaves _ _).mp (live a ha) i eq.symm)
    rw [add_comm] at h
    apply (cota_temporal_del_error_de_riesgo v qp tq.le l reg i e hp h1 slack low h).trans
    apply div_le_div_of_nonneg_left En (by positivity)
    have a:=mul_le_mul_of_nonneg_left (show (t:ℝ)≤q by exact_mod_cast tq.le) (sub_nonneg.mpr h1)
    linarith only [a]
  have bd:=deriva_del_tablero_antes_de_salir v qp l reg (f j) fn kn sm pos ref' load cell track
  apply bd.trans
  apply mul_le_mul_of_nonneg_right _ (show 0≤4*H+restoDePadre q η U by positivity)
  apply le_trans _ (margenes_del_tablero_fisico v l qp small err).2
  rw [tableroG,normalizador_real_del_paso_G]
  apply Finset.sum_le_sum
  intro e _
  by_cases live : ∀ b∈l,compatible e b
  · simp only [masaVivaEn,if_pos live,cuatro_familias_dan_el_peso_de_G v q t e (fun i=>(pos e i).le)]
    exact mul_le_of_le_one_right (NNReal.coe_nonneg _) (ft e)
  · simp only [masaVivaEn,if_neg live,le_refl]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_de_una_marca_tras_seguimiento
