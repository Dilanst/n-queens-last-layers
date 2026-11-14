import MomentoDeInnovaciones
import LibroRealCentrado
namespace ArticuloA.RealFinita
open ArticuloA.Trayectoria ArticuloA.Trayectoria.ProfileKernel ArticuloA.Trayectoria.Adjunto
open scoped NNReal
variable {X : Type}
theorem cola_libro (E : Momento.Exponencial) (step : Nat → X → Atoms ℝ≥0 X) (F G : Nat → X → ℝ≥0)
    (norm : ∀ t x, total masas (step t x) = 1) (B : ℝ≥0)
    (V : X → Prop) (inv : ∀ t x, V x → ∀ i ∈ step t x, V i.2)
    (jump : ∀ t x, V x → ∀ i ∈ step t x,
      within masas (F (t+1) i.2 + avg masas (step t x) (G (t+1)))
        (G (t+1) i.2 + avg masas (step t x) (F (t+1))) B)
    (t m : Nat) (h : HistoryBook X ℝ≥0) (good : V h.state)
    (θ a : ℝ) (pos : 0 ≤ θ) (small : θ*(B:ℝ) ≤ 1) :
    (avg masas (leaves masas (historyRow masas step F G) t m h)
      (mark masas (fun j => a ≤ saldo j))).val ≤
      E.fn ((m:ℝ)*(θ*B)^2 + θ*saldo h - θ*a) := by
  classical
  let row := historyRow masas step F G
  let ok := fun q : HistoryBook X ℝ≥0 => V q.state
  let guarded := onlyOn masas row ok
  have preserve (u v) (hv : ok v) (i) (hi : i ∈ row u v) : ok i.2 := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact inv _ _ hv _ hj
  rw [←restrict_leaves masas row ok preserve _ _ h good]
  obtain ⟨tot,cent,cap⟩ := libro_centrado step F G norm B V jump
  exact Momento.cola E guarded (fun _ => saldo) tot cent θ B pos small cap t m h a
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola_libro
