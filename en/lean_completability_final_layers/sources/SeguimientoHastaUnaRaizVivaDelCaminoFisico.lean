import FluctuacionesFisicasDeTableroMarcasYLineas
import TelescopadoHastaElPrimerIndiceDeSalida
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

def raizConservada {I : Type} {n} (j : IndiceDeSeguimiento n I) (l : List (Cell n)) : Prop :=
  match j with
  | .inl _=>True
  | .inr (i,z)=>∀ b∈l,llaveDeLinea i b≠llaveDeLinea i z

def observacionFisica {I : Type} {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : I→Cell n→ℝ)
    (j : IndiceDeSeguimiento n I) (t : ℕ) (l : List (Cell n)) : ℝ := match j with
  | .inl i=>pesoObservable (fun e=>pesoDeFamiliasG v q t e Finset.univ*f i e) (some l)
  | .inr (i,z)=>∑ e∈fibraFisicaG i z,masaVivaEn l (fun b=>pesoDeFamiliasG v q t b (Finset.univ.erase i)) e

theorem raiz_conservada_al_quitar {I : Type} {n} (j : IndiceDeSeguimiento n I) (l : List (Cell n)) (e : Cell n)
    (ok : raizConservada j (e::l)) : raizConservada j l := by
  cases j with
  | inl _=>trivial
  | inr ij=>obtain ⟨i,z⟩:=ij; exact fun b hb=>ok b (List.mem_cons_of_mem e hb)

theorem incremento_de_la_observacion_superviviente {I : Type} {n q} (v : Cell n→ℝ≥0)
    (f : I→Cell n→ℝ) (j : IndiceDeSeguimiento n I) (t : ℕ) (l : List (Cell n)) (e : Cell n)
    (ok : raizConservada j (e::l)) :
    incrementoFisicoDeG v q f j t (some l) (some (e::l))=
      observacionFisica v q f j (t+1) (e::l)-observacionFisica v q f j t l := by
  cases j with
  | inl _=>simp only [incrementoFisicoDeG,observacionFisica,deltaDeMasaEn,pesoObservable,Finset.sum_sub_distrib]
  | inr ij=>
    obtain ⟨i,z⟩:=ij
    have off:=ok e List.mem_cons_self
    simp [incrementoFisicoDeG,observacionFisica,fueraDeRaiz,off,deltaDeMasaEn,Finset.sum_sub_distrib]

theorem telescopado_del_mismo_camino {I : Type} {n q} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (j : IndiceDeSeguimiento n I) (hist : List (EstadoGuiado n)) (t : ℕ)
    (l last : List (Cell n)) (root : raizConservada j last)
    (path : transicionesDeCamino (pasoDeG v q) t (some l) hist)
    (guard : prefijoRegular (regionSeguraDelPaso v q) t (some l) hist)
    (endp : ultimoEstado (some l) hist=some last) (z : ℝ) :
    let Y:=incrementoFisicoDeG v q f j
    let drift:=fun t x (_ : EstadoGuiado n)=>media (pasoDeG v q t x) (Y t x)
    let D:=innovacionActiva (pasoDeG v q) (regionSeguraDelPaso v q) Y
    raizConservada j l ∧
    sumarPasos D t (some l) z hist+sumarPasos drift t (some l) 0 hist=
      z+observacionFisica v q f j (t+hist.length) last-observacionFisica v q f j t l := by
  let Y:=incrementoFisicoDeG v q f j
  let d:=fun t x (_ : EstadoGuiado n)=>media (pasoDeG v q t x) (Y t x)
  let D:=innovacionActiva (pasoDeG v q) (regionSeguraDelPaso v q) Y
  have offset (ys : List (EstadoGuiado n)) (u x) (c c' : ℝ) :
      sumarPasos d u x (c+c') ys=c+sumarPasos d u x c' ys:=by
    induction ys generalizing u x c' with
    | nil=>rfl
    | cons y rest ih=>simp only [sumarPasos,add_assoc]; exact ih (u+1) y _
  induction hist generalizing t l z with
  | nil=>
    have eq : l=last:=Option.some.inj endp
    subst last
    exact ⟨root,by simp [sumarPasos]⟩
  | cons y rest ih=>
    obtain ⟨⟨w,mem⟩,next⟩:=path
    obtain ⟨safe,g⟩:=guard
    have low:=safe.2.1
    have reg : total masas (opcionesGuiadas v q t l)≠0:=by
      intro no; rw [no] at low
      change (9/10:ℝ)*q≤0 at low
      have qr : 0<(q:ℝ):=by exact_mod_cast qp
      linarith
    obtain ⟨e,rfl,_,_⟩:=origen_regular_agrega_casilla v q t l reg w y mem
    let child:=some (e::l)
    obtain ⟨alive,tail⟩:=ih (t+1) (e::l) next g endp (z+D t (some l) child)
    refine ⟨raiz_conservada_al_quitar j l e alive,?_⟩
    have edge:=incremento_de_la_observacion_superviviente (q:=q) v f j t l e alive
    have start : D t (some l) child=Y t (some l) child-d t (some l) child:=if_pos safe
    have shift:=offset rest (t+1) child (d t (some l) child) 0
    rw [add_zero] at shift
    change sumarPasos D (t+1) child _ rest+sumarPasos d (t+1) child (0+d t (some l) child) rest=_
    rw [zero_add,shift]
    change sumarPasos D (t+1) child _ rest+sumarPasos d (t+1) child 0 rest=_ at tail
    change Y t (some l) child=_ at edge
    have tm : t+(child::rest).length=t+1+rest.length:=by simp; omega
    rw [tm]
    linarith only [tail,start,edge]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.telescopado_del_mismo_camino
