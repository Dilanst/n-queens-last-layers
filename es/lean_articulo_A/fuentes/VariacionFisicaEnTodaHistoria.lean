import PasosPositivosDeUnaHistoria
import HistoriasLegales
import PerdidaCorte
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Repair Corte
noncomputable section

theorem salto_del_contador_fisico {n} (w : ColorWeights ℝ≥0) (t : ℕ) (X : State n)
    (coh : coherent X) (i : ℝ≥0×State n) (mem : i∈kernel masas w (·⁻¹) t X) :
    coherent i.2 ∧ ∀ z : Cell n, |(physicalCount i.2.physical z:ℝ)-physicalCount X.physical z|≤4 := by
  rcases kernel_child masas w (·⁻¹) t X i mem with same | ⟨a,ad,eq⟩
  · rw [same]; exact ⟨coh,by simp⟩
  rw [eq]
  refine ⟨next_coherent coh a ad,?_⟩
  intro z
  cases a with
  | fail => simp [next]
  | virtual v => simp [next]
  | real e =>
    obtain ⟨lo,hi⟩:=step_counts X.physical z e coh.1 (choice_adm coh (.real e) ad)
    change |(physicalCount (toggle e X.physical) z:ℝ)-physicalCount X.physical z|≤4
    have a : (physicalCount X.physical z:ℝ)≤physicalCount (toggle e X.physical) z+4 := by exact_mod_cast lo
    have b : (physicalCount (toggle e X.physical) z:ℝ)≤physicalCount X.physical z+1 := by exact_mod_cast hi
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The physical observable is Lipschitz along the full padded trajectory, even after
failure. This is a statement about the law of the original process on its support. -/
theorem oscilacion_en_la_historia {n h T} (w : ColorWeights ℝ≥0) (i : ℝ≥0×List (State n))
    (mem : i∈rutas (kernel masas w (·⁻¹)) 0 T (initial n h)) (nz : i.1≠0)
    (u v : ℕ) (uv : u≤v) (vT : v≤T) (z : Cell n) :
    let X:=estadoEn (initial n h) i.2
    |(physicalCount (X v).physical z:ℝ)-physicalCount (X u).physical z|≤4*(↑(v-u):ℝ) := by
  intro X
  obtain ⟨_,chain⟩:=pasos_con_peso mem nz
  have good (j) (jj : j≤T) : coherent (X j) := by
    induction j with
    | zero => exact initial_coherent _ _
    | succ j ih =>
      obtain ⟨a,ha,_,eq⟩:=chain j (by omega)
      rw [←show a.2=X (j+1) from eq]
      exact (salto_del_contador_fisico w _ _ (ih (by omega)) a ha).1
  have path (d : ℕ) (room : u+d≤T) :
      |(physicalCount (X (u+d)).physical z:ℝ)-physicalCount (X u).physical z|≤4*(d:ℝ) := by
    induction d with
    | zero => simp
    | succ d ih =>
      obtain ⟨a,ha,_,eq⟩:=chain (u+d) (by omega)
      have step:=(salto_del_contador_fisico w _ _ (good (u+d) (by omega)) a ha).2 z
      rw [eq] at step
      have triangle:=abs_sub_le (physicalCount (X (u+d+1)).physical z:ℝ)
        (physicalCount (X (u+d)).physical z) (physicalCount (X u).physical z)
      change |(physicalCount (X (u+d+1)).physical z:ℝ)-physicalCount (X u).physical z|≤4*(↑(d+1):ℝ)
      rw [Nat.cast_add,Nat.cast_one]
      linarith [ih (by omega)]
  simpa only [Nat.add_sub_of_le uv] using path (v-u) (by omega)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscilacion_en_la_historia
