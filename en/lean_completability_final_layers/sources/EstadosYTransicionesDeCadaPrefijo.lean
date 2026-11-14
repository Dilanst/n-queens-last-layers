import SeguimientoHastaUnaRaizVivaDelCaminoFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

variable {X : Type}

theorem estado_del_prefijo_cero (x : X) (h : List X) : estadoTrasPrefijo x h 0=x := by cases h <;> rfl

theorem extremo_del_prefijo (h : List X) (x : X) (m : ℕ) :
    ultimoEstado x (h.take m)=estadoTrasPrefijo x h m := by
  induction m generalizing x h with
  | zero=>simp [ultimoEstado,estado_del_prefijo_cero]
  | succ m ih=>cases h with
    | nil=>rfl
    | cons y ys=>exact ih ys y

theorem transiciones_del_prefijo {P : ℕ→X→Atoms ℝ≥0 X} {t x} {h : List X}
    (p : transicionesDeCamino P t x h) (m : ℕ) : transicionesDeCamino P t x (h.take m) := by
  induction m generalizing h t x with
  | zero=>trivial
  | succ m ih=>cases h with
    | nil=>trivial
    | cons y ys=>exact ⟨p.1,ih p.2⟩

theorem arista_del_prefijo {P : ℕ→X→Atoms ℝ≥0 X} {t x} {h : List X}
    (p : transicionesDeCamino P t x h) (m : ℕ) (lt : m<h.length) :
    ∃ w,(w,estadoTrasPrefijo x h (m+1))∈P (t+m) (estadoTrasPrefijo x h m) := by
  induction m generalizing h t x with
  | zero=>cases h with
    | nil=>simp at lt
    | cons y ys=>simpa [estadoTrasPrefijo,estado_del_prefijo_cero] using p.1
  | succ m ih=>cases h with
    | nil=>simp at lt
    | cons y ys=>
      have eq : t+(m+1)=t+1+m:=by omega
      simpa only [eq,estadoTrasPrefijo] using ih p.2 (by simpa using lt)

theorem seguridad_hasta_el_ultimo_salto {V : ℕ→X→Prop} (t : ℕ) (x : X) (h : List X)
    (m : ℕ) (safe : ∀ j<m,V (t+j) (estadoTrasPrefijo x h j)) : prefijoRegular V t x (h.take m) := by
  induction m generalizing h t x with
  | zero=>trivial
  | succ m ih=>cases h with
    | nil=>trivial
    | cons y ys=>
      refine ⟨by simpa [estadoTrasPrefijo] using safe 0 (by omega),ih (t+1) y ys ?_⟩
      intro j hj
      have eq : t+(j+1)=t+1+j:=by omega
      simpa only [estadoTrasPrefijo,eq] using safe (j+1) (by omega)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.arista_del_prefijo
#print axioms ArticuloA.Historias.seguridad_hasta_el_ultimo_salto
