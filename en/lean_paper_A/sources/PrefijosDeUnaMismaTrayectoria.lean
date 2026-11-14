import ColaExponencialReal
import ConcentracionCoordenadaE2
open scoped NNReal
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte
noncomputable section
variable {X : Type}

def rutas (step : ℕ→X→Atoms ℝ≥0 X) (t : ℕ) : ℕ→X→Atoms ℝ≥0 (List X)
  | 0,_ => point masas []
  | k+1,x => bindAtoms masas (step t x) (fun y =>
      (rutas step (t+1) k y).map (fun i => (i.1,y::i.2)))

theorem masa_de_rutas (step : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (step t x)=1)
    (t k : ℕ) (x : X) : total masas (rutas step t k x)=1 := by
  unfold total
  induction k generalizing t x with
  | zero => rw [rutas,avg_point]; rfl
  | succ k ih =>
    rw [rutas,avg_bind]
    have eq (y : X) : avg masas ((rutas step (t+1) k y).map (fun i => (i.1,y::i.2))) (fun _ => masas.one)=1 :=
      (avg_push masas _ (fun tail => y::tail) _).trans (ih _ _)
    simp_rw [eq]
    exact norm t x

def leerLibro (step : ℕ→X→Atoms ℝ≥0 X) (F G : ℕ→X→ℝ≥0)
    (t : ℕ) (h : HistoryBook X ℝ≥0) : List X→HistoryBook X ℝ≥0
  | [] => h
  | y::tail => leerLibro step F G (t+1) (record masas step F G t h y) tail

theorem proyeccion_de_prefijo (step : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (step t x)=1)
    (F G : ℕ→X→ℝ≥0) (t m k : ℕ) (le : m≤k) (h : HistoryBook X ℝ≥0)
    (v : HistoryBook X ℝ≥0→ℝ≥0) :
    avg masas (rutas step t k h.state) (fun l => v (leerLibro step F G t h (l.take m))) =
      avg masas (leaves masas (historyRow masas step F G) t m h) v := by
  induction m generalizing t k h with
  | zero =>
    simp only [List.take_zero,leerLibro,leaves,avg_point]
    rw [E2.avg_constant,masa_de_rutas step norm]; exact one_mul _
  | succ m ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [rutas,leaves,avg_bind,avg_bind,historyRow,avg_push]
      apply congrArg (avg masas (step t h.state))
      funext y
      rw [avg_push]
      simp only [List.take_succ_cons,leerLibro]
      exact ih (t+1) k (by omega) (record masas step F G t h y)

def intercambiar (h : HistoryBook X ℝ≥0) : HistoryBook X ℝ≥0 :=
  ⟨h.state,h.neg,h.pos,h.driftNeg,h.driftPos⟩

theorem libro_invertido (step : ℕ→X→Atoms ℝ≥0 X) (F G : ℕ→X→ℝ≥0) (l : List X)
    (t : ℕ) (h : HistoryBook X ℝ≥0) :
    leerLibro step G F t (intercambiar h) l=intercambiar (leerLibro step F G t h l) := by
  induction l generalizing t h with
  | nil => rfl
  | cons y ys ih => exact ih (t+1) (record masas step F G t h y)

theorem saldo_invertido (h : HistoryBook X ℝ≥0) : saldo (intercambiar h) = -saldo h := by
  unfold intercambiar saldo; simp only; ring
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.proyeccion_de_prefijo
#print axioms ArticuloA.RealFinita.libro_invertido
