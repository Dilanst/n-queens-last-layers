import MasaDeUnaHistoriaComoProductoDeTransiciones
import EsperanzaDeUnCosteEnLaLeyAgregada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
variable {X : Type}

def entropiaDeEstados (xs : Atoms ℝ≥0 X) : ℝ :=
  ∑ x∈(xs.map Prod.snd).toFinset,-(masaAgregada xs x*log (masaAgregada xs x))

theorem entropia_como_media_de_la_informacion (xs : Atoms ℝ≥0 X) :
    entropiaDeEstados xs=media xs (fun x=> -log (masaAgregada xs x)) := by
  rw [media_con_peso_agregado xs _ (xs.map Prod.snd).toFinset
      (fun i h=>List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,h,rfl⟩))]
  unfold entropiaDeEstados
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem entropia_del_camino_es_media_de_coste (P : ℕ→X→Atoms ℝ≥0 X) (t k : ℕ) (x : X) :
    entropiaDeEstados (rutas P t k x)=media (rutas P t k x) (costeDeHistoria P t x) := by
  let xs:=rutas P t k x
  have cover (i : ℝ≥0×List X) (h : i∈xs) : i.2∈(xs.map Prod.snd).toFinset:=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,h,rfl⟩)
  unfold entropiaDeEstados
  convert (entropia_de_las_historias_como_coste_del_camino P t k x).trans
    (media_con_peso_agregado xs _ _ cover).symm using 1
  congr 1
  ext l
  simp

theorem cadena_de_entropia_del_camino (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ s y,total masas (P s y)=1)
    (t k : ℕ) (x : X) :
    entropiaDeEstados (rutas P t (k+1) x)=entropiaDeEstados (P t x)+
      media (P t x) (fun y=>entropiaDeEstados (rutas P (t+1) k y)) := by
  rw [entropia_del_camino_es_media_de_coste,rutas,media_de_una_eleccion_y_su_continuacion]
  have term (y : X) :
      media ((rutas P (t+1) k y).map (fun i=>(i.1,y::i.2))) (costeDeHistoria P t x)=
        -log (masaAgregada (P t x) y)+entropiaDeEstados (rutas P (t+1) k y):=by
    rw [media_de_una_funcion_tras_mapa]
    change media (rutas P (t+1) k y)
      (fun l=>-log (masaAgregada (P t x) y)+costeDeHistoria P (t+1) y l)=_
    have eq:=media_affine (rutas P (t+1) k y) (costeDeHistoria P (t+1) y) (-log (masaAgregada (P t x) y)) 1
    rw [masa_de_rutas _ norm] at eq
    norm_num [entropia_del_camino_es_media_de_coste] at eq ⊢
    exact eq
  simp_rw [term]
  rw [media_suma_de_dos_costes,←entropia_como_media_de_la_informacion]

theorem cadena_para_el_kernel_fisico {n} (v : Cell n→ℝ≥0) (q t k : ℕ) (x : EstadoGuiado n) :
    entropiaDeEstados (rutas (pasoDeG v q) t (k+1) x)=entropiaDeEstados (pasoDeG v q t x)+
      media (pasoDeG v q t x) (fun y=>entropiaDeEstados (rutas (pasoDeG v q) (t+1) k y)) :=
  cadena_de_entropia_del_camino _ (G_es_ley v q) _ _ _
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cadena_para_el_kernel_fisico
