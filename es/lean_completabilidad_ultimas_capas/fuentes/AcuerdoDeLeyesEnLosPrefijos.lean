import ProyeccionAlProcesoOriginal
import PasosPositivosDeUnaHistoria
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel Trayectoria.E2 Trayectoria.Adjunto RealFinita Corte
noncomputable section
open Classical

def prefijoAbierto {X : Type} (ok : ℕ→X→Bool) (t : ℕ) (x : X) : List X→Prop
  | [] => True
  | y::ys => ok t x=true ∧ prefijoAbierto ok (t+1) y ys

theorem prefijo_desde_indices {X : Type} (ok : ℕ→X→Bool) (t : ℕ) (x : X) (l : List X)
    (abierto : ∀ j<l.length,ok (t+j) (estadoEn x l j)=true) : prefijoAbierto ok t x l := by
  induction l generalizing x t with
  | nil => trivial
  | cons y l ih =>
    refine ⟨by simpa only [Nat.add_zero] using abierto 0 (by simp),ih (t+1) y ?_⟩
    intro j hj
    have step := abierto (j+1) (by simp only [List.length_cons]; omega)
    simpa only [Nat.add_right_comm,Nat.add_assoc,Nat.add_comm 1 j] using step

theorem ley_en_los_prefijos_abiertos {X : Type} (S U : ℕ→X→Atoms ℝ≥0 X) (ok : ℕ→X→Bool)
    (igual : ∀ j x,ok j x=true → S j x=U j x) (t T : ℕ) (x : X) (g : List X→ℝ≥0) :
    avg masas (rutas S t T x) (fun l => if prefijoAbierto ok t x l then g l else 0) =
    avg masas (rutas U t T x) (fun l => if prefijoAbierto ok t x l then g l else 0) := by
  classical
  induction T generalizing t x g with
  | zero => rfl
  | succ T ih =>
    rw [rutas,rutas,avg_bind,avg_bind]
    by_cases live : ok t x=true
    · rw [igual t x live]
      apply congrArg (avg masas _); funext y
      rw [avg_push,avg_push]
      simp only [prefijoAbierto,live,true_and]
      exact ih (t+1) y (fun l => g (y::l))
    · have nada {Y : Type} (l : Atoms ℝ≥0 Y) : avg masas l (fun _ => (0:ℝ≥0))=0 := by
        rw [avg_constant]; exact mul_zero _
      simp only [avg_push,prefijoAbierto,live,Bool.false_eq_true,false_and,if_false,nada]

theorem coherencia_en_el_prefijo {n} (w : ColorWeights ℝ≥0) (halt : ℕ→State n→Bool)
    (x : ℕ×State n) (hx : coherent x.2) (t T : ℕ) (i : ℝ≥0×List (ℕ×State n))
    (mem : i∈rutas (pasoParado w halt) t T x) (nz : i.1≠0) :
    ∀ j≤T,coherent (estadoEn x i.2 j).2 := by
  obtain ⟨_,steps⟩:=pasos_con_peso mem nz
  intro j hj
  induction j with
  | zero => exact hx
  | succ j ih =>
    obtain ⟨a,ha,_,eq⟩:=steps j (by omega)
    rw [←eq]; exact coherent_at_stop masas w (·⁻¹) halt _ _ (ih (by omega)) a ha

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ley_en_los_prefijos_abiertos
