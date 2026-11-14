import ProbabilidadDeFalloCuadraticaEnLaReservaDelArticulo
import ConteoDeSalidasDesdeLaEntropiaDeLaMismaLeyG
import EntropiaAcumuladaDeLasEleccionesDelTablero
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
def parcialesDeReserva {n} (m : ℕ) (D A : ℤ→Prop) : Finset (Finset (Cell n)) :=
  Finset.univ.filter (fun S=>SalidaDeReserva m D A (elegirCasillas S (board n)))

theorem pertenencia_al_conteo_de_reserva {n} (m : ℕ) (D A : ℤ→Prop) (S : Finset (Cell n)) :
    S∈parcialesDeReserva m D A↔SalidaDeReserva m D A (elegirCasillas S (board n)) := by simp [parcialesDeReserva]

theorem conteo_fisico_de_parciales_desde_las_elecciones {n q m : ℕ} (np : 0<n) (v : Cell n→ℝ≥0)
    (D A : ℤ→Prop) (d : ℝ≥0) (size : q+m=n) (small : falloDelParcialReservado v q m D A d<1) :
    let O:=parcialesDeReserva (n:=n) m D A
    let xs:=rutas (pasoDeG v q) 0 q (some [])
    O.Nonempty ∧ entropiaDeEstados xs-log q.factorial-log 2-
      falloDelParcialReservado v q m D A d*(2*q*log n)≤log (O.card:ℝ) := by
  classical
  intro O xs
  let S:=(xs.map Prod.snd).toFinset
  let g:=fun h=>prefijoRegular (condicionDeSeguimientoG v q (marcasDeG D A) d) 0 (some []) h ∧ salidaFisicaDeG m D A h
  have ne : ∃ h,g h:=by
    apply Classical.byContradiction
    intro impossible
    have all (h : List (EstadoGuiado n)) : ¬g h:=fun y=>impossible ⟨h,y⟩
    have flip : mark masas (fun h=>¬g h)=fun _=>(1:ℝ≥0):=by funext h; simp [mark,all h,masas]
    change (avg masas xs (mark masas (fun h=>¬g h))).val<1 at small
    rw [flip,show avg masas xs (fun _=>(1:ℝ≥0))=1 from masa_de_rutas _ (G_es_ley v q) _ _ _] at small
    exact (lt_irrefl (1:ℝ)) small
  obtain ⟨h,_,l,_,sal⟩:=ne
  have op : O.Nonempty:=⟨l.toFinset,(pertenencia_al_conteo_de_reserva _ _ _ _).mpr sal⟩
  have sz T (ht : T∈O) : T.card=q:=by
    have eq:=((pertenencia_al_conteo_de_reserva _ _ _ _).mp ht).2.1
    rw [←tamano_soporte,soporte_elegido] at eq
    omega
  have main:=conteo_desde_la_entropia_de_la_misma_ley_G np v (marcasDeG D A) d O op sz
  let good:=S.filter (fun h=>prefijoRegular (condicionDeSeguimientoG v q (marcasDeG D A) d) 0 (some []) h ∧
    ∃ l,ultimoEstado (some []) h=some l ∧ l.toFinset∈O)
  have bound :
      (avg masas xs (mark masas (·∈S\good))).val≤falloDelParcialReservado v q m D A d:=by
    apply NNReal.coe_le_coe.mpr
    apply avg_mono
    intro a _
    by_cases yes : a.2∈S\good
    · have both:=Finset.mem_sdiff.mp yes
      have fail : ¬g a.2:=by
        rintro ⟨gu,l,ep,ok⟩
        exact both.2 (Finset.mem_filter.mpr ⟨both.1,gu,l,ep,(pertenencia_al_conteo_de_reserva _ _ _ _).mpr ok⟩)
      change mark masas _ _≤mark masas (fun h=>¬g h) _
      simp [mark,yes,fail,masas]
    · simp [mark,yes,masas]
  have logpos : 0≤log (n:ℝ):=Real.log_nonneg (by exact_mod_cast np)
  have penalty:=mul_le_mul_of_nonneg_right bound (by positivity : 0≤2*(q:ℝ)*log n)
  have clean : entropiaDeEstados xs-log q.factorial-log 2-
      (avg masas xs (mark masas (·∈S\good))).val*(2*q*log n)≤log (O.card:ℝ) := by
    have ent : entropiaDeEstados xs=∑ l∈S,-(masaAgregada xs l*log (masaAgregada xs l)):=by
      unfold entropiaDeEstados
      apply Finset.sum_congr _ (fun _ _=>rfl)
      ext l
      simp [S]
    rw [ent]
    exact main
  exact ⟨op,by linarith only [clean,penalty]⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.conteo_fisico_de_parciales_desde_las_elecciones
