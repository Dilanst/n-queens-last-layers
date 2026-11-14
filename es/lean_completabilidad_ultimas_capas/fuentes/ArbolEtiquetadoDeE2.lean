import EsperanzaRealFinita
import FilaEfectiva
import CuotasDelEstado
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n : ℕ}
abbrev Registro (n : ℕ) := List (Choice n) × State n
def ramas (x : State n) (w : ColorWeights ℝ≥0) : Atoms ℝ≥0 (Choice n × State n) :=
  if x.failed || (x.reals+x.virtuals==0) then point masas (.fail,x)
  else (choices masas x w (·⁻¹)).map (fun b => (b.1,b.2,next x b.2))

theorem proyectar_paso (x : State n) (w : ColorWeights ℝ≥0) (t : ℕ) (f : State n → ℝ≥0) :
    avg masas (ramas x w) (fun y => f y.2) = avg masas (kernel masas w (·⁻¹) t x) f := by
  unfold ramas
  split
  · rename_i stop
    rw [kernel,if_pos stop,avg_point,avg_point]
  · rename_i sigue
    have live : x.failed=false := by cases bit : x.failed <;> simp_all
    have quedan : x.reals+x.virtuals≠0 := by intro nope; exact sigue (by simp [nope])
    rw [kernel_is_row masas _ _ _ _ live quedan]
    rw [avg_push masas _ (next x) f]
    exact avg_push masas _ (fun a : Choice n => (a,next x a)) (fun y => f y.2)

def arbol (w : ColorWeights ℝ≥0) : ℕ → State n → Atoms ℝ≥0 (Registro n)
  | 0,x => point masas ([],x)
  | m+1,x => bindAtoms masas (ramas x w) (fun b =>
    (arbol w m b.2).map (fun d => (d.1,b.1::d.2.1,d.2.2)))

theorem proyectar_arbol (w : ColorWeights ℝ≥0) (m t : ℕ) (x : State n) (f : State n → ℝ≥0) :
    avg masas (arbol w m x) (fun b => f b.2) = avg masas (leaves masas (kernel masas w (·⁻¹)) t m x) f := by
  induction m generalizing t x with
  | zero => rw [arbol,leaves,avg_point,avg_point]
  | succ m ih =>
    rw [arbol,leaves,avg_bind,avg_bind]
    apply Eq.trans _ (proyectar_paso x w t (fun y => avg masas (leaves masas (kernel masas w (·⁻¹)) (t+1) m y) f))
    apply congrArg (avg masas (ramas x w))
    funext b
    exact (avg_push masas (arbol w m b.2) (fun d : Registro n => (b.1::d.1,d.2)) (fun y => f y.2)).trans (ih (t+1) b.2)

theorem concatenar_rama (w : ColorWeights ℝ≥0) (m : ℕ) (x y z : State n)
    (a : Choice n) (p v : ℝ≥0) (path : List (Choice n))
    (step : (p,a,y)∈ramas x w) (tail : (v,path,z)∈arbol w m y) :
    (p*v,a::path,z)∈arbol w (m+1) x := by
  rw [arbol,bindAtoms]
  exact List.mem_flatMap.mpr ⟨_,step,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,tail,rfl⟩,rfl⟩⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.proyectar_arbol
#print axioms ArticuloA.Historias.concatenar_rama
