import SumaConjuntaDelTableroYUnaRaiz
import DerivaConjuntaDeUnPadreFisico
import InnovacionYDerivaHastaUnaObservacionReal
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem error_en_el_extremo_real {I : Type} {n q t} (v : Cell n→ℝ≥0) (qp : 0<q)
    (f : I→Cell n→ℝ) (i0 : I) (one : ∀ e,f i0 e=1) (h : List (EstadoGuiado n))
    (path : transicionesDeCamino (pasoDeG v q) 0 (some []) h) (len : t≤h.length)
    (l : List (Cell n)) (endp : estadoTrasPrefijo (some []) h t=some l)
    (safe : ∀ s<t,regionSeguraDelPaso v q s (estadoTrasPrefijo (some []) h s))
    (pos : ∀ s≤t,∀ e j,0<fraccionVivaG v q s e j) (mass : ∑ e,(v e:ℝ)=q)
    (cw cz : ℝ) (czn : 0≤cz) (gain : ℕ→ℝ)
    (bw : |innovacionDePrefijo v q f (.inl i0) h t|≤cw)
    (bz : ∀ i z,|innovacionDePrefijo v q f (.inr (i,z)) h t|≤cz)
    (drift : ∀ s<t,
      let d:=fun j=>derivaFisica v q f j s (estadoTrasPrefijo (some []) h s)
      |d (.inl i0)|/q≤gain s ∧ ∀ i z,|d (.inl i0)|/q+|d (.inr (i,z))|≤gain s) :
    sigueTableroYLineas v q t l (cw/q+cz+∑ s∈Finset.range t,gain s) := by
  let d (j : IndiceDeSeguimiento n I) (s : ℕ):=derivaFisica v q f j s (estadoTrasPrefijo (some []) h s)
  have w0:=(W_inicia_con_la_masa_de_entrada v q).trans mass
  have ew:=descomposicion_del_prefijo_fisico v qp f (.inl i0) h len path l endp trivial safe
  rw [observacion_de_tablero_constante v l f i0 one (pos t le_rfl),
    observacion_de_tablero_constante v [] f i0 one (pos 0 (Nat.zero_le _)),show tableroG v q 0 []=q from w0] at ew
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  constructor
  · have bnd:=suma_de_dos_innovaciones_y_derivas (t:=t) (Z:=0) (mz:=0) qr (d (.inl i0))
      (fun _=>0) gain bw (by simpa using czn) ew (by simp)
      (fun s hs=>by simpa using (drift s hs).1)
    simpa using bnd
  · intro i z live
    have ez:=descomposicion_del_prefijo_fisico v qp f (.inr (i,z)) h len path l endp live safe
    change _+(∑ s∈Finset.range t,d (.inr (i,z)) s)=
      (∑ e∈fibraFisicaG i z,masaVivaEn l (fun b=>pesoDeFamiliasG v q t b (Finset.univ.erase i)) e)-
      (∑ e∈fibraFisicaG i z,masaVivaEn [] (fun b=>pesoDeFamiliasG v q 0 b (Finset.univ.erase i)) e) at ez
    rw [Z_es_la_suma_de_tres_familias v l i z (pos t le_rfl),
      Z_es_la_suma_de_tres_familias v [] i z (pos 0 (Nat.zero_le _)),Z_inicia_en_la_masa_de_su_linea] at ez
    exact suma_de_dos_innovaciones_y_derivas qr (d (.inl i0)) (d (.inr (i,z))) gain bw (bz i z) ew ez
      (fun s hs=>(drift s hs).2 i z)

theorem ampliar_error_de_seguimiento {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n)) {a b : ℝ}
    (err : sigueTableroYLineas v q t l a) (ab : a≤b) : sigueTableroYLineas v q t l b :=
  ⟨err.1.trans ab,fun i z root=>(err.2 i z root).trans ab⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_en_el_extremo_real
