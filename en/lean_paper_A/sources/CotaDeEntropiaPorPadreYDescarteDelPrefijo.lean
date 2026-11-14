import EntropiaDeLaCasillaDesdeLaMarcaSeguida
import DeLosErroresRelativosALasMarcasDeB2
import MediaDeUnaSumaDeMarcas
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
theorem lado_bueno_del_normalizador {W E q : ℝ} (qp : 0<q) (en : 0≤E) (es : E≤1/2)
    (bd : |W-q|/q≤E) : log q-2*E≤log W := by
  have ep : 0<1-E:=by linarith
  have z:=(abs_le.mp ((div_le_iff₀ qp).mp bd)).1
  have cmp : q*(1-E)≤W:=by linarith only [z,mul_sub q 1 E,mul_one q,mul_comm q E]
  have lg:=Real.log_le_log (mul_pos qp ep) cmp
  rw [Real.log_mul qp.ne' ep.ne'] at lg
  have a:=Real.log_le_sub_one_of_pos (inv_pos.mpr ep)
  rw [Real.log_inv] at a
  have top : (1-E)⁻¹≤1+2*E:=by
    rw [←one_div]; apply (div_le_iff₀ ep).mpr
    nlinarith only [mul_nonneg en (show 0≤1-2*E by linarith)]
  linarith only [lg,a,top]

theorem base_y_lineas_de_un_padre {I : Type} {n q t : ℕ} (np : 0<n) (qp : 0<q) (v : Cell n→ℝ≥0)
    (l : List (Cell n)) (f : I→Cell n→ℝ) (j : I) {E b L : ℝ} (en : 0≤E) (es : E≤1/10) (lp : 0≤L)
    (mass : ∑ e,(v e:ℝ)=q) (fz : ∀ e,0≤f j e ∧ f j e≤1)
    (repr : ∀ e,marcaLogaritmica ((n:ℝ)^2) (v e)=L*f j e)
    (pos : ∀ e i,0<fraccionVivaG v q t e i) (err : sigueTableroYLineas v q t l E)
    (bv : |observacionFisica v q f (.inl j) t l-(∑ e,(v e:ℝ)*f j e)|/q≤b) :
    log (q:ℝ)-(∑ e,(v e:ℝ)*log (v e:ℝ))/q-(2*E+1/q+2*L*(E+b))+
      (∑ e,leyDePieza v q t l e*∑ i,log (fraccionVivaG v q t e i))≤entropiaDeEstados (pasoDeG v q t (some l)) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have low:=(margenes_del_tablero_fisico v l qp es err).1
  have reg : total masas (opcionesGuiadas v q t l)≠0:=by
    intro zero; rw [tableroG,zero] at low; change (9/10:ℝ)*q≤0 at low; linarith
  have w:=lado_bueno_del_normalizador qr en (es.trans (by norm_num)) err.1
  have c:=entropia_de_la_casilla_en_un_padre_seguido v l f j (sq_pos_of_pos nr) lp qp mass fz repr reg
    (fun e i=>(pos e i).le) (by linarith) err.1 bv
  have b0:=div_le_div_of_nonneg_right (truncamiento_agregado_de_la_entrada np v mass) qr.le
  rw [add_div,add_div,mul_div_cancel_left₀ _ qr.ne'] at b0
  rw [entropia_del_padre_fisico v l reg pos]
  change log (q:ℝ)-_-_+_≤log (tableroG v q t l)-_+_
  linarith only [c,b0,w]

theorem entropia_no_negativa_de_una_ley {X : Type} (xs : Atoms ℝ≥0 X) (norm : total masas xs=1) :
    0≤entropiaDeEstados xs := by
  unfold entropiaDeEstados
  apply Finset.sum_nonneg
  intro x _
  have cmp:=avg_mono masas xs (mark masas (fun y=>y=x)) (fun _=>1) (by
    intro a _; by_cases eq : a.2=x <;> simp [mark,eq,masas])
  have top : masaAgregada xs x≤1:=by
    change (avg masas xs _).val≤1
    change avg masas xs _≤total masas xs at cmp
    rw [norm] at cmp
    exact_mod_cast cmp
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (NNReal.coe_nonneg _)
    (Real.log_nonpos (NNReal.coe_nonneg _) top))

theorem descartar_prefijos_por_su_parte_positiva {X : Type} (xs : Atoms ℝ≥0 X) (norm : total masas xs=1)
    (keep : X→Prop) (ent line : X→ℝ) {B U prob : ℝ} (un : 0≤U) (bu : B≤U)
    (bad : (avg masas xs (mark masas (fun x=>¬keep x))).val≤prob)
    (nonneg : ∀ x,0≤ent x) (localBound : ∀ x,keep x→B+line x≤ent x) :
    B-prob*U+media xs (fun x=>if keep x then line x else 0)≤media xs ent := by
  let fail (x : X):=(mark masas (fun y=>¬keep y) x).val
  let c (x : X):=if keep x then line x else 0
  have point (x : X) : B+(-U)*fail x+c x≤ent x:=by
    by_cases yes : keep x
    · simpa [fail,c,yes,mark,masas] using localBound x yes
    · simpa [fail,c,yes,mark,masas] using (show B+-U≤ent x by linarith only [bu,nonneg x])
  have m:=media_mono xs (fun x=>B+(-U)*fail x+c x) ent (fun a _=>point a.2)
  rw [media_suma_de_dos_costes,media_affine,norm] at m
  have eq:=media_coe xs (mark masas (fun y=>¬keep y))
  have cmp:=mul_le_mul_of_nonneg_right (eq.le.trans bad) un
  change _+media xs c≤_ at m
  change _+media xs c≤_
  change media xs fail*U≤prob*U at cmp
  change (1:ℝ)*B+(-U)*media xs fail+media xs c≤media xs ent at m
  rw [one_mul] at m
  linarith only [m,cmp,neg_mul U (media xs fail),mul_comm U (media xs fail)]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.base_y_lineas_de_un_padre
#print axioms ArticuloA.Historias.descartar_prefijos_por_su_parte_positiva
