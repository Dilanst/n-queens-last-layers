import EntropiaAcumuladaDeLasEleccionesDelTablero
import UnaLeyParaTodasLasRaicesYTiempos
import MediaDeUnaSumaDeMarcas
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

variable {X : Type}
theorem media_real_del_prefijo (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (P t x)=1)
    (g : List X→ℝ) (t j T : ℕ) (jt : j≤T) (x : X) :
    media (rutas P t T x) (fun l=>g (l.take j))=media (rutas P t j x) g := by
  induction j generalizing t T x g with
  | zero=>
    simp only [List.take_zero,rutas]
    have a:=media_affine (rutas P t T x) (fun _=>0) (g []) 0
    rw [masa_de_rutas _ norm] at a
    change media _ (fun _=>g [])=(1:ℝ)*g []+0
    norm_num at a ⊢
    exact a
  | succ j ih=>
    cases T with
    | zero=>omega
    | succ T=>
      rw [rutas,rutas,media_de_una_eleccion_y_su_continuacion,media_de_una_eleccion_y_su_continuacion]
      apply congrArg (media (P t x))
      funext y
      rw [media_de_una_funcion_tras_mapa,media_de_una_funcion_tras_mapa]
      simpa only [List.take_succ_cons] using ih (fun l=>g (y::l)) (t+1) T (by omega) y

theorem coste_de_padres_indexado (H : ℕ→X→ℝ) (t : ℕ) (x : X) (l : List X) :
    costeDeLosPadres H t x l=∑ i∈Finset.range l.length,H (t+i) (ultimoEstado x (l.take i)) := by
  induction l generalizing x t with
  | nil=>simp [costeDeLosPadres]
  | cons y l ih=>
    rw [costeDeLosPadres,ih,List.length_cons,Finset.sum_range_succ']
    simp only [List.take_zero,List.take_succ_cons,ultimoEstado,Nat.add_zero]
    rw [add_comm]
    apply congrArg (·+H t x)
    apply Finset.sum_congr rfl
    intro i _
    congr 1; omega

theorem entropia_como_suma_de_las_leyes_en_cada_tiempo (P : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (P t x)=1)
    (x : X) (q : ℕ) :
    entropiaDeEstados (rutas P 0 q x)=∑ t∈Finset.range q,
      media (rutas P 0 t x) (fun hist=>entropiaDeEstados (P t (ultimoEstado x hist))) := by
  let H s y:=entropiaDeEstados (P s y)
  let Q:=rutas P 0 q x
  let F (t : ℕ) (l : List X):=H t (ultimoEstado x (l.take t))
  have pt (a : ℝ≥0×List X) (ha : a∈Q) :
      costeDeLosPadres H 0 x a.2=∑ t∈Finset.range q,F t a.2:=by
    rw [coste_de_padres_indexado,(rutas_siguen_su_ley P 0 q x a ha).2]
    simp only [F,Nat.zero_add]
  rw [entropia_acumulada_sobre_los_padres P norm]
  have eq := le_antisymm
    (media_mono Q (costeDeLosPadres H 0 x) (fun l=>∑ t∈Finset.range q,F t l) (fun a ha=>(pt a ha).le))
    (media_mono Q (fun l=>∑ t∈Finset.range q,F t l) (costeDeLosPadres H 0 x) (fun a ha=>(pt a ha).ge))
  change media Q (costeDeLosPadres H 0 x)=_
  rw [eq,media_de_suma_finita]
  apply Finset.sum_congr rfl
  intro t ht
  exact media_real_del_prefijo P norm (fun hist=>H t (ultimoEstado x hist)) 0 t q (Finset.mem_range.mp ht).le x
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_como_suma_de_las_leyes_en_cada_tiempo
