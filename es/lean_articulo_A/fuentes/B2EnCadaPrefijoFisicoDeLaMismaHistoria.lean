import SeguimientoDeLasMarcasEnLaMismaHistoria
import DeLosErroresRelativosALasMarcasDeB2
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem B2_sobre_el_mismo_camino {I : Type} {n q : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (i0 : I) (one : ∀ e,f i0 e=1) (fn : ∀ i e,0≤f i e) (ft : ∀ i e,f i e≤1)
    (S : Cell n→Cell n→Prop) (j : Cell n→I) (repr : ∀ z e,f (j z) e=(mark masas (S z) e).val)
    (d : ℝ≥0) (marks : ∀ z,(d:ℝ)*q≤∑ e,(v e:ℝ)*(mark masas (S z) e).val)
    (h : List (EstadoGuiado n)) (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h)
    (len : h.length=q) (mass : ∑ e,(v e:ℝ)=q) {η U A cw cz : ℝ} (hp : 0<η) (h4 : η≤1/4)
    (up : 0≤U) (cap : ∀ e,(v e:ℝ)≤U) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (sm : (5/4)/(η*q)≤1/16) (an : 0≤A) (wn : 0≤cw) (zn : 0≤cz)
    (tiny : A*(1/η)^12≤1/80) (markTol : 8*(A*(1/η)^12)/η≤(d:ℝ)/16)
    (budget : cw/q+cz+(22/10)*q*restoDePadre q η U≤A)
    (bw : ∀ t≤q,∀ i,|innovacionDePrefijo v q f (.inl i) h t|≤cw)
    (bz : ∀ t≤q,∀ i z,|innovacionDePrefijo v q f (.inr (i,z)) h t|≤cz) :
    prefijoRegular (condicionDeSeguimientoG v q S d) 0 (some []) h := by
  let E:=A*(1/η)^12
  have small : E≤1/10:=tiny.trans (by norm_num)
  have en : 0≤E:=by dsimp [E]; positivity
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have h1 : η≤1:=by linarith only [h4]
  have rn : 0≤restoDePadre q η U:=by unfold restoDePadre; positivity
  have ae : A≤E:=le_mul_of_one_le_right an (one_le_pow₀ ((one_le_div hp).mpr h1))
  have bound:=costo_de_una_marca_en_funcion_del_error hp h1 qr wn zn rn ae budget
  have realpath:=no_hay_primera_salida_en_el_camino v qp f i0 one h path len mass hp h4 up cap slack sm
    an small zn budget (fun t ht=>bw t ht i0) bz
  have get s (sq : s≤q) : ∃ l,estadoTrasPrefijo (some []) h s=some l ∧ sigueTableroYLineas v q s l E:=by
    obtain ⟨l,ep,err⟩:=realpath s sq
    exact ⟨l,ep,ampliar_error_de_seguimiento v l err (techo_del_umbral qp sq hp h4 an)⟩
  have all t (tq : t<q) : condicionDeSeguimientoG v q S d t (estadoTrasPrefijo (some []) h t):=by
    obtain ⟨l,ep,err⟩:=get t tq.le
    rw [ep]
    apply condicion_B2_de_las_desviaciones v qp l S d tiny err marks
    intro z
    have b:=marca_seguida_hasta_el_extremo v qp f (j z) (fn _) (ft _) h path len tq.le l ep hp h1 up cap slack
      sm en small (fun s st=>get s (st.le.trans tq.le)) (bw t tq.le (j z))
    rw [observacion_de_un_conjunto_marcado v l f (j z) (S z) (repr z)
      (fun e i=>hp.trans_le (margen_de_fraccion_viva qp tq.le v slack h1 e i))] at b
    simp_rw [repr z] at b
    exact b.trans (bound.trans markTol)
  have guard:=seguridad_hasta_el_ultimo_salto (V:=condicionDeSeguimientoG v q S d)
    0 (some []) h q (fun t ht=>by simpa using all t ht)
  simpa only [←len,List.take_length] using guard
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.B2_sobre_el_mismo_camino
