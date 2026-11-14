import FluctuacionesFisicasDeTableroMarcasYLineas
import ReservaFisicaConstruidaDesdeElOptimoContinuo
import ParametrosDeLasColasEnLaReservaDelArticulo
namespace ArticuloA.Historias
open Repair Perfil RealFinita Trayectoria Trayectoria.ProfileKernel Real Filter
open scoped NNReal BigOperators Topology
noncomputable section
open Classical

def colaParaTodasLasMarcas {n} (v : Cell n→ℝ≥0) (q : ℕ) (η U : ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin m→Cell n→ℝ), (∀ i e,0≤f i e)→(∀ i e,f i e≤1)→
    let J:=IndiceDeSeguimiento n (Fin m)
    let B:J→ℝ:=escalaDelSalto n q η U
    let D:=fun j : J=>innovacionActiva (pasoDeG v q) (regionSeguraDelPaso v q) (incrementoFisicoDeG v q f j)
    (avg masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fun l=>∃ j : J,∃ r : Fin (q+1),
      2*B j*sqrt (q:ℝ)*log n≤|sumarPasos (D j) 0 (some []) 0 (l.take r.val)|))).val≤
      (Fintype.card J:ℝ)*(q+1)*(2*exp (-(log (n:ℝ))^2))

theorem existe_reserva_fisica_con_cola_simultanea :
    ∃ (κ A C : ℝ),0<κ ∧ 0<A ∧ 0≤C ∧ ∀ᶠ n : ℕ in atTop,
    let q:=n-huecosReserva n
    let x:=fraccionReserva n
    let τ:=(n:ℝ)^(-exponenteReserva)
    let η:=κ*x/4
    ∃ (u : LineaReservable n→Bool) (v : Cell n→ℝ≥0),
      (∑ e,(v e:ℝ))=q ∧ (∀ e,(v e:ℝ)≤2*(A/n)) ∧ (∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) ∧
      (∀ e,v e≠0→¬oblicuaMarcada u etiquetaD 2 (llaveDeLinea 2 e) ∧ ¬oblicuaMarcada u etiquetaA 3 (llaveDeLinea 3 e)) ∧
      (∀ z,τ^4*(q:ℝ)/8≤masaBajo (fun e=>(v e:ℝ)) (marcasDeG (oblicuaMarcada u etiquetaD 2) (oblicuaMarcada u etiquetaA 3) z)) ∧
      (q:ℝ)*log n+n*sSup valoresCartesianosDeAbsorcion-C-constanteB1 κ*τ*n*log (1/x)≤
        entropiaDiscretaDeReserva (fun e=>(v e:ℝ)) ∧ colaParaTodasLasMarcas v q η (2*(A/n)) := by
  obtain ⟨P,p,κ,A,C,kp,ap,cp,phys⟩:=existe_reserva_del_optimo_fisico
  refine ⟨κ,A,C,kp,ap,cp,?_⟩
  filter_upwards [phys,parametros_del_seguimiento_en_la_reserva kp] with n src bounds
  obtain ⟨comp,_,_,_,u,_,mass,cap,slack,ent,marks⟩:=src
  obtain ⟨np,qp,hp,ht,risk,lg,scale⟩:=bounds
  intro q x τ η
  let w:=cargaCelda n q (p x)
  let b:=(q:ℝ)/(∑ e,pesoRetenido w u e)
  let raw:=fun e=>b*pesoRetenido w u e
  let v:=fun e=>Real.toNNReal (raw e)
  have realv (e) : (v e:ℝ)=raw e:=Real.coe_toNNReal _ (cap e).1
  have high (e) : (v e:ℝ)≤2*(A/n):=by rw [realv e]; exact (cap e).2
  have load (j e) : (masaDeLineaG v j e:ℝ)≤1-η:=by
    rw [masa_de_linea_en_G_es_la_de_B1]
    simp_rw [realv]
    exact slack _
  refine ⟨u,v,?_,high,load,?_,?_,?_,?_⟩
  · simp_rw [realv]; exact mass
  · intro e nz
    apply el_peso_retenido_evita_ambas_marcas w b u
    change raw e≠0
    rw [←realv]; exact_mod_cast nz
  · intro z; simp_rw [realv]; exact marks z
  · simp_rw [realv]
    apply le_trans _ ent
    have v0:=mul_le_mul_of_nonneg_left comp (Nat.cast_nonneg (α:=ℝ) n)
    linarith only [v0]
  · intro m f fn ft
    have nr : 0<(n:ℝ):=by exact_mod_cast np
    have h1 : η≤1:=by change η≤1/4 at ht; linarith
    have u : 0<2*(A/n):=by positivity
    have small : 1/(η*q)≤1/16:=(div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤5/4)
      (mul_nonneg hp.le (Nat.cast_nonneg _))).trans risk
    exact cola_fisica_de_todas_las_innovaciones np v qp f fn ft hp h1 u small high load lg scale
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existe_reserva_fisica_con_cola_simultanea
