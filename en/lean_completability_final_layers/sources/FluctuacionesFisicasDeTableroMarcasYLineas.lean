import ColaSimultaneaDeLosPrefijosDelProcesoG
import CotasDeLosRiesgosAntesDeLaPrimeraSalida
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def regionSeguraDelPaso {n} (v : Cell n→ℝ≥0) (q t : ℕ) : EstadoGuiado n→Prop
  | none=>False
  | some l=>t<q ∧ (9/10:ℝ)*q≤(total masas (opcionesGuiadas v q t l)).val ∧
      ∀ i e,masaObservadaDeLinea v q t l i e≤11/10

abbrev IndiceDeSeguimiento (n : ℕ) (I : Type) := I ⊕ (Fin 4×Cell n)

def incrementoFisicoDeG {I : Type} {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : I→Cell n→ℝ)
    (j : IndiceDeSeguimiento n I) (t : ℕ) : EstadoGuiado n→EstadoGuiado n→ℝ
  | none,_=>0
  | some l,y=>match j with
    | .inl i=>
      let a:=fun t' e=>pesoDeFamiliasG v q t' e Finset.univ*f i e
      deltaDeMasaEn l Finset.univ (a t) (a (t+1)) y
    | .inr (i,z)=>
      let a:=fun t' e=>pesoDeFamiliasG v q t' e (Finset.univ.erase i)
      if fueraDeRaiz i z y then deltaDeMasaEn l (fibraFisicaG i z) (a t) (a (t+1)) y else 0

def escalaDelSalto {I : Type} (n q : ℕ) (η U : ℝ) : IndiceDeSeguimiento n I→ℝ
  | .inl _=>4*n*(U/η^4)
  | .inr _=>(11/10)*(6*(1/(η*q)))+3*(U/η^3)

theorem saltos_efectivos_en_la_region_segura {I : Type} {n q : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (fn : ∀ i e,0≤f i e) (ft : ∀ i e,f i e≤1)
    {η U : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0≤U) (small : 1/(η*q)≤1/16)
    (cap : ∀ e,(v e:ℝ)≤U) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    (j : IndiceDeSeguimiento n I) (t : ℕ) (x : EstadoGuiado n) (ok : regionSeguraDelPaso v q t x)
    (b : ℝ≥0×EstadoGuiado n) (hb : b∈pasoDeG v q t x) :
    let Y:=incrementoFisicoDeG v q f j t x
    |Y b.2-media (pasoDeG v q t x) Y|≤escalaDelSalto n q η U j := by
  cases x with
  | none=>exact False.elim ok
  | some l=>
    obtain ⟨tq,low,top⟩:=ok
    have qr : 0<(q:ℝ):=by exact_mod_cast qp
    have reg : total masas (opcionesGuiadas v q t l)≠0:=by
      intro z; rw [z] at low; change (9/10:ℝ)*q≤0 at low; linarith
    obtain ⟨e,ee,_,_⟩:=origen_regular_agrega_casilla v q t l reg b.1 b.2 hb
    rw [ee]
    have hπ (e i):=margen_de_fraccion_viva qp (Nat.succ_le_of_lt tq) v slack h1 e i
    cases j with
    | inl i=>
      have bnd:=salto_de_W_con_holgura v l reg hp up cap hπ (f i) (fn i) (ft i) zero_le_one e
      simpa only [mul_one] using bnd
    | inr ij=>
      obtain ⟨i,z⟩:=ij
      have u:=(riesgos_antes_de_salir v qp tq.le l reg hp h1 up cap slack low top).1
      have h0 (e j):=hp.trans_le (margen_de_fraccion_viva qp tq.le v slack h1 e j)
      have kn : 0≤1/(η*(q:ℝ)):=by positivity
      have bnd:=salto_de_Z_con_holgura v qp l reg i z kn small hp up h0 u cap hπ e
      exact bnd.trans (add_le_add_right (mul_le_mul_of_nonneg_right (top i z) (by positivity)) _)

theorem cola_fisica_de_todas_las_innovaciones {I : Type} [Fintype I] {n q : ℕ} (np : 0<n)
    (v : Cell n→ℝ≥0) (qp : 0<q) (f : I→Cell n→ℝ) (fn : ∀ i e,0≤f i e) (ft : ∀ i e,f i e≤1)
    {η U : ℝ} (hp : 0<η) (h1 : η≤1) (up : 0<U) (small : 1/(η*q)≤1/16)
    (cap : ∀ e,(v e:ℝ)≤U) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    {a : ℝ} (ap : 0≤a) (scale : a≤sqrt (q:ℝ)) :
    let J:=IndiceDeSeguimiento n I
    let B:J→ℝ:=escalaDelSalto n q η U
    let D:=fun j : J=>innovacionActiva (pasoDeG v q) (regionSeguraDelPaso v q) (incrementoFisicoDeG v q f j)
    (avg masas (rutas (pasoDeG v q) 0 q (some [])) (mark masas (fun l=>∃ j : J,∃ m : Fin (q+1),
      2*B j*sqrt (q:ℝ)*a≤|sumarPasos (D j) 0 (some []) 0 (l.take m.val)|))).val≤
      (Fintype.card (IndiceDeSeguimiento n I):ℝ)*(q+1)*(2*exp (-(a^2))) := by
  have bp (j : IndiceDeSeguimiento n I) : 0<escalaDelSalto n q η U j:=by
    cases j with
    | inl _=>dsimp [escalaDelSalto]; positivity
    | inr _=>dsimp [escalaDelSalto]; positivity
  exact innovaciones_simultaneas_de_G v (fun _=>regionSeguraDelPaso v q) (incrementoFisicoDeG v q f)
    (escalaDelSalto n q η U) bp qp (saltos_efectivos_en_la_region_segura v qp f fn ft hp h1 up.le small cap slack)
    (some []) a ap scale
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_fisica_de_todas_las_innovaciones
