import ProbabilidadDeUnaLineaVivaAntesDelCorte
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def usoDeLineaEnEstado {n} (v : Cell n→ℝ≥0) (q t : ℕ) (i : Fin 4) (z : Cell n) : EstadoGuiado n→ℝ
  | none=>0
  | some l=>riesgoDeLinea (leyDePieza v q t l) z i

theorem vida_del_extremo_implica_vida_en_el_prefijo {n q t} (v : Cell n→ℝ≥0) (qp : 0<q)
    (i : Fin 4) (z : Cell n) {E : ℝ} (small : E≤1/10) (l : List (Cell n)) (h : List (EstadoGuiado n))
    (path : transicionesDeCamino (pasoDeG v q) t (some l) h)
    (good : prefijoRegular (guardaDelErrorFisico v q E) t (some l) h)
    (last : lineaVivaEnEstado i z (ultimoEstado (some l) h)) :
    lineaVivaEnEstado i z (some l) ∧ caminoVivo (guardaDelErrorFisico v q E) (lineaVivaEnEstado i z) t (some l) h := by
  induction h generalizing t l with
  | nil=>exact ⟨last,last⟩
  | cons y ys ih=>
    obtain ⟨⟨w,mem⟩,path'⟩:=path
    obtain ⟨parent,good'⟩:=good
    have low:=(margenes_del_tablero_fisico v l qp small parent).1
    have reg : total masas (opcionesGuiadas v q t l)≠0:=by
      intro zero
      rw [tableroG,zero] at low
      change (9/10:ℝ)*q≤0 at low
      have qr : 0<(q:ℝ):=by exact_mod_cast qp
      linarith
    obtain ⟨b,rfl,_,_⟩:=origen_regular_agrega_casilla v q t l reg w y mem
    obtain ⟨child,rest⟩:=ih (t:=t+1) (b::l) path' good' last
    have start : lineaVivaEnEstado i z (some l):=fun e he=>child e (List.mem_cons_of_mem _ he)
    exact ⟨start,parent,start,rest⟩

theorem esperanza_de_uso_de_linea_en_prefijos {n q t : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t≤q)
    (i : Fin 4) (z : Cell n) {η E : ℝ} (hp : 0<η) (h1 : η≤1) (en : 0≤E) (es : E≤1/10)
    (sm : 1/(η*q)≤1/2) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    (keep : List (EstadoGuiado n)→Prop) (ok : ∀ hist,keep hist→
      prefijoRegular (guardaDelErrorFisico v q E) 0 (some []) hist ∧
        guardaDelErrorFisico v q E t (ultimoEstado (some []) hist)) :
    let H:=E/((9/10)*η*q)
    media (rutas (pasoDeG v q) 0 t (some [])) (fun h=>if keep h then
      usoDeLineaEnEstado v q t i z (ultimoEstado (some []) h) else 0)≤
        exp (2*H*t)*((masaDeLineaG v i z:ℝ)/q+H*fraccionVivaG v q t z i) := by
  classical
  let H:=E/((9/10)*η*q)
  let u:=riesgoPrevisto v q t z i
  let πt:=fraccionVivaG v q t z i
  let law:=rutas (pasoDeG v q) 0 t (some [])
  let alive:=caminoVivo (guardaDelErrorFisico v q E) (lineaVivaEnEstado i z) 0 (some [])
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have pp : 0<πt:=hp.trans_le (margen_de_fraccion_viva qp tq v slack h1 z i)
  have hn : 0≤H:=by dsimp [H]; positivity
  have un : 0≤u:=div_nonneg (NNReal.coe_nonneg _) (mul_nonneg qr.le pp.le)
  have per (a : ℝ≥0×List (EstadoGuiado n)) (mem : a∈law) :
      (if keep a.2 then usoDeLineaEnEstado v q t i z (ultimoEstado (some []) a.2) else 0)≤
        (u+H)*(mark masas alive a.2).val:=by
    have rhs : 0≤(u+H)*(mark masas alive a.2).val:=mul_nonneg (add_nonneg un hn) (NNReal.coe_nonneg _)
    by_cases yes : keep a.2
    · rw [if_pos yes]
      obtain ⟨path,_⟩:=rutas_siguen_su_ley _ _ _ _ a mem
      obtain ⟨guard,endpoint⟩:=ok a.2 yes
      cases eq : ultimoEstado (some []) a.2 with
      | none=>rw [eq] at endpoint; exact False.elim endpoint
      | some l=>
        rw [eq] at endpoint
        have low:=(margenes_del_tablero_fisico v l qp es endpoint).1
        have reg : total masas (opcionesGuiadas v q t l)≠0:=by
          intro zero; rw [tableroG,zero] at low; change (9/10:ℝ)*q≤0 at low; linarith
        by_cases live : lineaVivaEnEstado i z (some l)
        · have ep : lineaVivaEnEstado i z (ultimoEstado (some []) a.2):=eq ▸ live
          have aLive:=(vida_del_extremo_implica_vida_en_el_prefijo v qp i z es [] a.2 path guard ep).2
          have bv:=endpoint.2 i z live
          rw [add_comm] at bv
          have err:=cota_temporal_del_error_de_riesgo v qp tq l reg i z hp h1 slack low bv
          have ht : E/((9/10)*((q:ℝ)-(1-η)*t))≤H:=by
            apply div_le_div_of_nonneg_left en (by positivity)
            have h:=mul_le_mul_of_nonneg_left (show (t:ℝ)≤q by exact_mod_cast tq) (sub_nonneg.mpr h1)
            linarith only [h]
          have bd:=(abs_le.mp (err.trans ht)).2
          change alive a.2 at aLive
          simp only [mark,if_pos aLive,masas,NNReal.coe_one,mul_one]
          norm_num
          change riesgoDeLinea _ _ _≤u+H
          dsimp only [u]; linarith only [bd]
        · have hit : ∃ b∈l,llaveDeLinea i b=llaveDeLinea i z:=by
            apply Classical.byContradiction
            intro no
            exact live (fun b hb same=>no ⟨b,hb,same⟩)
          change riesgoDeLinea _ _ _≤_
          rw [riesgo_de_linea_desde_Z v q t l reg i z pp,linea_ocupada_tiene_masa_observada_cero v l i z hit,zero_div]
          exact rhs
    · simpa only [if_neg yes] using rhs
  have cmp:=media_mono law (fun h=>if keep h then usoDeLineaEnEstado v q t i z (ultimoEstado (some []) h) else 0)
    (fun h=>(u+H)*(mark masas alive h).val) per
  have lin:=media_affine law (fun h=>(mark masas alive h).val) 0 (u+H)
  simp only [zero_add,mul_zero] at lin
  rw [lin] at cmp
  have mass:=media_coe law (mark masas alive)
  have prob:=masa_de_linea_viva_y_padres_regulares v qp tq i z hp h1 en es sm slack
  apply (cmp.trans (mul_le_mul_of_nonneg_left (mass.le.trans prob) (add_nonneg un hn))).trans_eq
  change (u+H)*(πt*exp (2*H*t))=_
  dsimp [u,riesgoPrevisto]
  change ((masaDeLineaG v i z:ℝ)/((q:ℝ)*πt)+H)*(πt*exp (2*H*t))=exp (2*H*t)*((masaDeLineaG v i z:ℝ)/q+H*πt)
  field_simp [qr.ne',pp.ne']; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.esperanza_de_uso_de_linea_en_prefijos
