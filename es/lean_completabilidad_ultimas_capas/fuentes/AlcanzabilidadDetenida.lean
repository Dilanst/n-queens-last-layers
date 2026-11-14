import HistoriasLegales
import ColaFinita
namespace ArticuloA.Trayectoria.ProfileKernel
open ArticuloA.Corte
variable {X Y α : Type} (s : ProfileScale α)

open Classical in
noncomputable def onlyOn (step : Nat → X → Atoms α X) (V : X → Prop) (t : Nat) (x : X) :=
  if V x then step t x else point s x

theorem bind_on_support (xs : Atoms α X) (f g : X → Atoms α Y)
    (eq : ∀ i ∈ xs, f i.2 = g i.2) : bindAtoms s xs f = bindAtoms s xs g := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    change (f i.2).map _ ++ bindAtoms s xs f = (g i.2).map _ ++ bindAtoms s xs g
    rw [eq i (by simp),ih (fun j hj => eq j (by simp [hj]))]

theorem restrict_leaves (step : Nat → X → Atoms α X) (V : X → Prop)
    (invar : ∀ t x, V x → ∀ i ∈ step t x, V i.2) (t m : Nat) (x : X) (hx : V x) :
    leaves s (onlyOn s step V) t m x = leaves s step t m x := by
  induction m generalizing x t with
  | zero => rfl
  | succ m ih =>
    simp only [leaves,onlyOn,hx,if_pos]
    apply bind_on_support
    intro i hi; exact ih (t+1) i.2 (invar t x hx i hi)

theorem stopped_invariant (step : Nat → X → Atoms α X) (halt : Nat → X → Bool) (V : X → Prop)
    (invar : ∀ t x, V x → ∀ i ∈ step t x, V i.2) (u : Nat) (v : Nat × X) (hv : V v.2)
    (i : α × (Nat × X)) (hi : i ∈ stopped s step halt u v) : V i.2.2 := by
  unfold stopped at hi; split at hi
  · obtain rfl := List.mem_singleton.mp hi
    exact hv
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact invar _ _ hv j hj

end ArticuloA.Trayectoria.ProfileKernel
namespace ArticuloA.Trayectoria.E2
open ArticuloA.Corte ProfileKernel
theorem coherent_at_stop {n α} (s : ProfileScale α) (w : ColorWeights α) (inv : α → α)
    (halt : Nat → State n → Bool) (u : Nat) (v : Nat × State n) (good : coherent v.2)
    (i : α × (Nat × State n)) (mem : i ∈ stopped s (kernel s w inv) halt u v) :
    coherent i.2.2 := by
  apply stopped_invariant s _ halt coherent _ u v good i mem
  intro t x hx j hj
  rcases kernel_child s w inv t x j hj with eq | ⟨a,ok,eq⟩
  · simpa only [eq] using hx
  · rw [eq]; exact next_coherent hx a ok
end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.ProfileKernel.restrict_leaves
#print axioms ArticuloA.Trayectoria.E2.coherent_at_stop
