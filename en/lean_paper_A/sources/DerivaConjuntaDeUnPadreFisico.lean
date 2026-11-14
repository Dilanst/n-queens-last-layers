import ErrorFisicoYSeguridadDeCadaPadre
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

abbrev derivaFisica {I : Type} {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : I→Cell n→ℝ)
    (j : IndiceDeSeguimiento n I) (t : ℕ) (state : EstadoGuiado n) :=
  media (pasoDeG v q t state) (incrementoFisicoDeG v q f j t state)

def restoDePadre (q : ℕ) (η U : ℝ) := 100*((5/4)/(η*q))^2+6*((U/η^4)/((9/10)*q))

theorem deriva_fisica_del_padre {I : Type} {n q t : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t<q)
    (l : List (Cell n)) (f : I→Cell n→ℝ) (i0 : I) (one : ∀ e,f i0 e=1)
    {η U b : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0≤U) (cap : ∀ e,(v e:ℝ)≤U)
    (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η) (sm : (5/4)/(η*q)≤1/16)
    (small : b≤1/10) (err : sigueTableroYLineas v q t l b) :
    let D:=(q:ℝ)-(1-η)*t
    let R:=restoDePadre q η U
    let d:=fun j=>derivaFisica v q f j t (some l)
    |d (.inl i0)|/q≤9/D*b+(22/10)*R ∧
      ∀ i z, |d (.inl i0)|/q+|d (.inr (i,z))|≤9/D*b+(22/10)*R := by
  let D:=(q:ℝ)-(1-η)*t
  let H:=b/((9/10)*D)
  let κ:=(5/4)/(η*q)
  let pm:=(U/η^4)/((9/10)*q)
  let R:=restoDePadre q η U
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have dp : 0<D:=by
    have ub:=mul_le_mul_of_nonneg_left (show (t:ℝ)≤q by exact_mod_cast tq.le) (sub_nonneg.mpr h1)
    dsimp [D]; nlinarith only [ub,mul_pos hp qr]
  have kn : 0≤κ:=by dsimp [κ]; positivity
  have rn : 0≤R:=by dsimp [R,restoDePadre]; positivity
  have bn : 0≤b:=(by positivity : 0≤|tableroG v q t l-q|/(q:ℝ)).trans err.1
  have safe:=regularidad_del_padre_fisico v qp tq l hp.le small slack err
  obtain ⟨_,low,top⟩:=safe
  have reg : total masas (opcionesGuiadas v q t l)≠0:=by
    intro no; rw [no] at low; change (9/10:ℝ)*q≤0 at low; linarith
  have pos e i:=hp.trans_le (margen_de_fraccion_viva qp tq.le v slack h1 e i)
  obtain ⟨ref,load,cell⟩:=riesgos_antes_de_salir v qp tq.le l reg hp h1 up cap slack low top
  have ref' e i : riesgoPrevisto v q t e i≤κ:=(ref e i).trans
    (div_le_div_of_nonneg_right (by norm_num) (mul_nonneg hp.le qr.le))
  have track e (live : ∀ a∈l,compatible e a) i :
      |riesgoPrevisto v q t e i-riesgoDeLinea (leyDePieza v q t l) e i|≤H:=by
    rw [abs_sub_comm]
    apply cota_temporal_del_error_de_riesgo v qp tq.le l reg i e hp h1 slack low
    rw [add_comm]
    exact err.2 i e (fun a ha eq=>(compatible_iff_llaves _ _).mp (live a ha) i eq.symm)
  have wb:=deriva_del_tablero_antes_de_salir v qp l reg (f i0) (fun e=>by rw [one]; norm_num)
    kn sm pos ref' load cell track
  change |derivaFisica v q f (.inl i0) t (some l)|≤observacionFisica v q f (.inl i0) t l*(4*H+R) at wb
  rw [observacion_de_tablero_constante v l f i0 one pos] at wb
  have wh:=(margenes_del_tablero_fisico v l qp small err).2
  dsimp only
  constructor
  · have z : |(0:ℝ)|≤0*(3*H+R):=by simp
    simpa using coeficiente_nueve_en_el_seguimiento qr dp bn rn wh (by norm_num : (0:ℝ)≤11/10) wb z
  · intro i z
    have zb:=deriva_de_Z_antes_de_salir v qp l reg i z kn sm pos ref' load cell track
    exact coeficiente_nueve_en_el_seguimiento qr dp bn rn wh (top i z) wb zb

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_fisica_del_padre
