import LineasFisicasEnLaEntropiaDeLasHistorias
import ColaDelPrefijoConLaMarcaDeEntropia
import CotaDeEntropiaPorPadreYDescarteDelPrefijo
import EntropiaDeHistoriasComoSumaDePrefijos
import FactorialYEntropiaDeEntradaPorEleccion
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem entropia_de_la_trayectoria_con_error_finito {I : Type} {n q : ℕ} (np : 0<n) (qp : 0<q)
    (v : Cell n→ℝ≥0) (f : I→Cell n→ℝ) (j : I) {η E L P : ℝ}
    (hp : 0<η) (h1 : η≤1) (en : 0≤E) (small : E≤1/10) (lp : 0≤L)
    (mass : ∑ e,(v e:ℝ)=q) (sz : ∀ e,0≤f j e ∧ f j e≤1)
    (repr : ∀ e,marcaLogaritmica ((n:ℝ)^2) (v e)=L*f j e)
    (sm : 1/(η*q)≤1/2) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (tail : ∀ t<q,(avg masas (rutas (pasoDeG v q) 0 t (some []))
      (mark masas (fun hist=>¬prefijoParaEntropia v q f j η E t hist))).val≤P) :
    let H:=E/((9/10)*η*q)
    let b:=exp (2*H*q)
    entropiaDiscretaDeReserva (fun e=>(v e:ℝ))-
        (2+log q+(q:ℝ)*(2*E+2*L*(E+8*E/η)+P*(2*log n))+4*q*((b-1)+b*H*q)/η)≤
      entropiaDeEstados (rutas (pasoDeG v q) 0 q (some []))-log q.factorial := by
  classical
  intro H b
  let Q t:=rutas (pasoDeG v q) 0 t (some [])
  let keep:=prefijoParaEntropia v q f j η E
  let vals:=∑ e,(v e:ℝ)*log (v e:ℝ)
  let U:=2*log n
  let B:=log (q:ℝ)-vals/q-(2*E+1/q+2*L*(E+8*E/η))
  let lines t (hist : List (EstadoGuiado n)):=aporteFisicoDeLineas v q t (ultimoEstado (some []) hist)
  let ent t (hist : List (EstadoGuiado n)):=entropiaDeEstados (pasoDeG v q t (ultimoEstado (some []) hist))
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have lg:=Real.log_nonneg (show (1:ℝ)≤n by exact_mod_cast np)
  have un : 0≤U:=by dsimp [U]; positivity
  have cost : 0≤2*E+1/(q:ℝ)+2*L*(E+8*E/η):=by positivity
  have bu : B≤U:=(sub_le_self _ cost).trans (cota_superior_de_la_base_por_celda np qp v mass)
  have per t (ht : t<q) : B-P*U+
      media (Q t) (fun hist=>if keep t hist then lines t hist else 0)≤media (Q t) (ent t):=by
    apply descartar_prefijos_por_su_parte_positiva (Q t) (masa_de_rutas _ (G_es_ley v q) _ _ _)
      (keep t) (ent t) (lines t) un bu (tail t ht)
    · intro h
      exact entropia_no_negativa_de_una_ley _ (G_es_ley v q _ _)
    · intro h ok
      obtain ⟨_,l,ep,safe,mark⟩:=ok
      dsimp only [lines,ent]
      rw [ep]
      exact base_y_lineas_de_un_padre np qp v l f j en small lp mass sz repr
        (fun e i=>hp.trans_le (margen_de_fraccion_viva qp ht.le v slack h1 e i)) safe mark
  have line:=aporte_esperado_de_las_cuatro_familias v qp mass hp h1 en small sm slack keep (by
    intro t _ h k
    obtain ⟨prev,l,ep,safe,_⟩:=k
    exact ⟨prev,by rw [ep]; exact safe⟩)
  have s:=Finset.sum_le_sum (s:=Finset.range q) (fun t ht=>per t (Finset.mem_range.mp ht))
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at s
  have chain:=entropia_como_suma_de_las_leyes_en_cada_tiempo (pasoDeG v q) (G_es_ley v q) (some []) q
  change entropiaDeEstados (rutas (pasoDeG v q) 0 q (some []))=∑ t∈Finset.range q,media (Q t) (ent t) at chain
  rw [←chain] at s
  have merged:=(add_le_add_left line ((q:ℝ)*(B-P*U))).trans s
  have fac:=log_factorial_superior_para_el_camino q qp
  have cell : entropiaCeldas (fun e=>(v e:ℝ))= -vals:=by
    simp only [entropiaCeldas,aporteCelda,neg_mul,Finset.sum_neg_distrib,vals]
  rw [entropiaDiscretaDeReserva,cell,mass]
  dsimp only [B,U] at merged
  change (q:ℝ)*(log q-vals/q-(2*E+1/q+2*L*(E+8*E/η))-P*(2*log n))+
      (entropiaLineas _-4*q-4*q*((b-1)+b*H*q)/η)≤_ at merged
  have div1 : (q:ℝ)*(1/q)=1:=by field_simp
  have divv : (q:ℝ)*(vals/q)=vals:=by field_simp
  nlinarith only [merged,fac,div1,divv]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_la_trayectoria_con_error_finito
