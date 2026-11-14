import ErroresFisicosDesdeLasInnovacionesDelCamino
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem no_hay_primera_salida_en_el_camino {I : Type} {n q} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (i0 : I) (one : ∀ e,f i0 e=1) (h : List (EstadoGuiado n))
    (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h) (length : h.length=q)
    (mass : ∑ e,(v e:ℝ)=q) {η U A cw cz : ℝ} (hp : 0<η) (h4 : η≤1/4)
    (up : 0≤U) (cap : ∀ e,(v e:ℝ)≤U) (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η)
    (sm : (5/4)/(η*q)≤1/16) (an : 0≤A) (tiny : A*(1/η)^12≤1/10) (czn : 0≤cz)
    (budget : cw/q+cz+(22/10)*q*restoDePadre q η U≤A)
    (bw : ∀ t≤q,|innovacionDePrefijo v q f (.inl i0) h t|≤cw)
    (bz : ∀ t≤q,∀ i z,|innovacionDePrefijo v q f (.inr (i,z)) h t|≤cz) :
    ∀ t≤q,∃ l,estadoTrasPrefijo (some []) h t=some l ∧ sigueTableroYLineas v q t l (umbralDePrefijo q η A t) := by
  let B:=umbralDePrefijo q η A
  let state:=estadoTrasPrefijo (some []) h
  let R:=restoDePadre q η U
  have h1 : η≤1:=by linarith only [h4]
  have rn : 0≤R:=by dsimp [R,restoDePadre]; positivity
  have top t (ht : t≤q) : B t≤1/10:=(techo_del_umbral qp ht hp h4 an).trans tiny
  have pos s (hs : s≤q) e i:=hp.trans_le (margen_de_fraccion_viva qp hs v slack h1 e i)
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih=>
    intro tq
    have safe s (st : s<t) : regionSeguraDelPaso v q s (state s):=by
      obtain ⟨l,eq,err⟩:=ih s st (st.le.trans tq)
      change regionSeguraDelPaso v q s (estadoTrasPrefijo (some []) h s)
      rw [eq]
      exact regularidad_del_padre_fisico v qp (st.trans_le tq) l hp.le (top s (st.le.trans tq)) slack err
    have existsEnd : ∃ l,state t=some l:=by
      cases t with
      | zero=>exact ⟨[],estado_del_prefijo_cero _ _⟩
      | succ s=>exact extremo_real_del_paso_seguro v qp h path (by omega) (safe s (by omega))
    obtain ⟨l,eq⟩:=existsEnd
    refine ⟨l,eq,?_⟩
    let gain (s : ℕ):=9/((q:ℝ)-(1-η)*s)*B s+(22/10)*R
    have drift s (st : s<t) :
        let d:=fun j=>derivaFisica v q f j s (state s)
        |d (.inl i0)|/q≤gain s ∧ ∀ i z,|d (.inl i0)|/q+|d (.inr (i,z))|≤gain s:=by
      obtain ⟨p,ep,err⟩:=ih s st (st.le.trans tq)
      change state s=some p at ep
      dsimp only
      rw [ep]
      exact deriva_fisica_del_padre v qp (st.trans_le tq) p f i0 one hp h1 up cap slack sm (top s (st.le.trans tq)) err
    have err:=error_en_el_extremo_real v qp f i0 one h path (length.symm ▸ tq) l eq safe
      (fun s hs=>pos s (hs.trans tq)) mass cw cz czn gain (bw t tq) (bz t tq) drift
    exact ampliar_error_de_seguimiento v l err (absorber_resto_constante_en_umbral tq rn budget)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.no_hay_primera_salida_en_el_camino
