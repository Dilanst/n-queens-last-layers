import RelojDelPrefijoRegular
import DescomposicionEnLaHistoriaDetenida
open scoped NNReal
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
variable {X : Type}

theorem ley_al_olvidar_el_reloj (S : ℕ→X→Atoms ℝ≥0 X) (t T : ℕ) (x : X) (F : List X→ℝ≥0) :
    avg masas (rutas (stopped masas S (fun _ _ => false)) t T (t,x)) (fun l => F (l.map Prod.snd)) =
      avg masas (rutas S t T x) F := by
  induction T generalizing t x F with
  | zero => simp only [rutas,avg_point,List.map_nil]
  | succ T ih =>
    rw [rutas,rutas,avg_bind,avg_bind]
    change avg masas ((S t x).map (fun i => (i.1,(t+1,i.2)))) _ = _
    rw [avg_push]; apply congrArg (avg masas (S t x)); funext y
    rw [avg_push,avg_push]
    exact ih (t+1) y (fun l => F (y::l))

theorem estado_al_olvidar_el_reloj (t : ℕ) (x : X) (l : List (ℕ×X)) (s : ℕ) :
    (estadoEn (t,x) l s).2=estadoEn x (l.map Prod.snd) s := by
  induction l generalizing x t s with
  | nil => simp [estadoEn]
  | cons y l ih =>
    cases s with
    | zero => rfl
    | succ s => exact ih y.1 y.2 s

end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.ley_al_olvidar_el_reloj
#print axioms ArticuloA.RealFinita.estado_al_olvidar_el_reloj
