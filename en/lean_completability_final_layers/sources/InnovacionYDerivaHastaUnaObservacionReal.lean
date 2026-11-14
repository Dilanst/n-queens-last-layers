import EstadosYTransicionesDeCadaPrefijo
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def innovacionDePrefijo {I : Type} {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : I→Cell n→ℝ)
    (j : IndiceDeSeguimiento n I) (h : List (EstadoGuiado n)) (t : ℕ) : ℝ :=
  sumarPasos (innovacionActiva (pasoDeG v q) (regionSeguraDelPaso v q) (incrementoFisicoDeG v q f j))
    0 (some []) 0 (h.take t)

theorem descomposicion_del_prefijo_fisico {I : Type} {n q t} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (j : IndiceDeSeguimiento n I) (h : List (EstadoGuiado n)) (le : t≤h.length)
    (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h) (last : List (Cell n))
    (endp : estadoTrasPrefijo (some []) h t=some last) (root : raizConservada j last)
    (safe : ∀ s<t,regionSeguraDelPaso v q s (estadoTrasPrefijo (some []) h s)) :
    let state:=estadoTrasPrefijo (some []) h
    innovacionDePrefijo v q f j h t+
      (∑ s∈Finset.range t,media (pasoDeG v q s (state s)) (incrementoFisicoDeG v q f j s (state s)))=
      observacionFisica v q f j t last-observacionFisica v q f j 0 [] := by
  have guard:=seguridad_hasta_el_ultimo_salto (V:=regionSeguraDelPaso v q) 0 (some []) h t
    (fun s hs=>by simpa using safe s hs)
  have fin:=(extremo_del_prefijo h (some []) t).trans endp
  have eq:=(telescopado_del_mismo_camino v qp f j (h.take t) 0 [] last root
    (transiciones_del_prefijo path t) guard fin 0).2
  change innovacionDePrefijo v q f j h t+sumarPasos
    (fun s x (_ : EstadoGuiado n)=>media (pasoDeG v q s x) (incrementoFisicoDeG v q f j s x)) 0 (some []) 0 (h.take t)=_ at eq
  rw [cuenta_de_aristas_del_prefijo (fun s x (_ : EstadoGuiado n)=>media (pasoDeG v q s x)
    (incrementoFisicoDeG v q f j s x)) 0 h (some []) 0 t le] at eq
  simpa only [innovacionDePrefijo,Nat.zero_add,zero_add,List.length_take,Nat.min_eq_left le] using eq

theorem extremo_real_del_paso_seguro {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (h : List (EstadoGuiado n))
    (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h) (ht : t<h.length)
    (safe : regionSeguraDelPaso v q t (estadoTrasPrefijo (some []) h t)) :
    ∃ last,estadoTrasPrefijo (some []) h (t+1)=some last := by
  obtain ⟨w,mem⟩:=arista_del_prefijo path t ht
  rw [Nat.zero_add] at mem
  cases e : estadoTrasPrefijo (some []) h t with
  | none=>rw [e] at safe; exact False.elim safe
  | some l=>
    rw [e] at mem safe
    have reg : total masas (opcionesGuiadas v q t l)≠0:=by
      intro no
      have low:=safe.2.1
      rw [no] at low
      change (9/10:ℝ)*q≤0 at low
      have qr : 0<(q:ℝ):=by exact_mod_cast qp
      linarith
    obtain ⟨b,eq,_,_⟩:=origen_regular_agrega_casilla v q t l reg w _ mem
    exact ⟨b::l,eq⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.descomposicion_del_prefijo_fisico
#print axioms ArticuloA.Historias.extremo_real_del_paso_seguro
