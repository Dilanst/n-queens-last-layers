import ReglaDeLaCadenaParaLaEntropiaDelCaminoG
import EntropiaCondicionalDeUnaEleccionFisica
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
variable {X : Type}

def costeDeLosPadres (H : ℕ→X→ℝ) (t : ℕ) (x : X) : List X→ℝ
  | []=>0
  | y::l=>H t x+costeDeLosPadres H (t+1) y l

theorem entropia_acumulada_sobre_los_padres (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ s y,total masas (P s y)=1)
    (t k : ℕ) (x : X) :
    entropiaDeEstados (rutas P t k x)=media (rutas P t k x) (costeDeLosPadres (fun s y=>entropiaDeEstados (P s y)) t x) := by
  let H s y:=entropiaDeEstados (P s y)
  induction k generalizing x t with
  | zero=>rw [entropia_del_camino_es_media_de_coste]; rfl
  | succ k ih=>
    rw [cadena_de_entropia_del_camino P norm,rutas,media_de_una_eleccion_y_su_continuacion]
    have term (y : X) :
        media ((rutas P (t+1) k y).map (fun i=>(i.1,y::i.2))) (costeDeLosPadres H t x)=
          H t x+entropiaDeEstados (rutas P (t+1) k y):=by
      rw [media_de_una_funcion_tras_mapa,ih]
      have a:=media_affine (rutas P (t+1) k y) (costeDeLosPadres H (t+1) y) (H t x) 1
      rw [masa_de_rutas P norm] at a
      norm_num at a
      exact a
    change H t x+_ = media (P t x) (fun y=>media _ (costeDeLosPadres H t x))
    simp_rw [term]
    have a:=media_affine (P t x) (fun y=>entropiaDeEstados (rutas P (t+1) k y)) (H t x) 1
    rw [norm] at a
    norm_num at a
    exact a.symm

theorem entropia_del_padre_fisico {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (pos : ∀ e i,0<fraccionVivaG v q t e i) :
    entropiaDeEstados (pasoDeG v q t (some l))=log (total masas (opcionesGuiadas v q t l)).val-
        (∑ e,leyDePieza v q t l e*log (v e:ℝ))+
        ∑ e,leyDePieza v q t l e*∑ i,log (fraccionVivaG v q t e i) := by
  rw [entropia_como_media_de_la_informacion,media_del_paso_fisico v q t l reg]
  apply Eq.trans _ (entropia_de_la_eleccion_fisica v l reg pos)
  apply Finset.sum_congr rfl
  intro e _
  change leyDePieza v q t l e*(-log (leyDePieza v q t l e))=_
  ring

theorem entropia_posterior_al_fallo {n} (v : Cell n→ℝ≥0) (q t : ℕ) :
    entropiaDeEstados (pasoDeG v q t none)=0 := by
  rw [entropia_como_media_de_la_informacion]
  change media [(1,none)] _=0
  simp [media,masaAgregada,pasoDeG,avg_point,mark,masas]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_acumulada_sobre_los_padres
#print axioms ArticuloA.Historias.entropia_del_padre_fisico
