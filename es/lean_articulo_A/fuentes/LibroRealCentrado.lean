import EsperanzaRealFinita
import MasaDeColor
import AlcanzabilidadDetenida
namespace ArticuloA.RealFinita
open ArticuloA.Trayectoria ArticuloA.Trayectoria.ProfileKernel ArticuloA.Trayectoria.Adjunto
open scoped NNReal
variable {X Y : Type}

theorem media_map (xs : Atoms ℝ≥0 X) (f : X → Y) (g : Y → ℝ) :
    media (xs.map (fun i => (i.1,f i.2))) g = media xs (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,media,ih]

def saldo (h : HistoryBook X ℝ≥0) : ℝ := (h.pos:ℝ) - h.neg

theorem libro_centrado (step : Nat → X → Atoms ℝ≥0 X) (F G : Nat → X → ℝ≥0)
    (norm : ∀ t x, total masas (step t x) = 1) (B : ℝ≥0)
    (V : X → Prop)
    (jump : ∀ t x, V x → ∀ i ∈ step t x,
      within masas (F (t+1) i.2 + avg masas (step t x) (G (t+1)))
        (G (t+1) i.2 + avg masas (step t x) (F (t+1))) B) :
    let row := historyRow masas step F G
    let guarded := onlyOn masas row (fun h : HistoryBook X ℝ≥0 => V h.state)
    (∀ u v, total masas (guarded u v) = 1) ∧
    (∀ u v, media (guarded u v) (fun y => saldo y - saldo v) = 0) ∧
    (∀ u v i, i ∈ guarded u v → |saldo i.2 - saldo v| ≤ (B:ℝ)) := by
  classical
  intro row guarded
  refine ⟨?_,?_,?_⟩
  · intro u v
    by_cases hv : V v.state
    · simp only [guarded,onlyOn,hv,if_true,row,historyRow,total,avg_push]; exact norm _ _
    · simp only [guarded,onlyOn,hv,if_false,total,avg_point]; rfl
  · intro u v
    by_cases hv : V v.state
    · simp only [guarded,onlyOn,hv,if_true,row,historyRow,media_map]
      let r := step u v.state
      let P y := F (u+1) y + avg masas r (G (u+1))
      let N y := G (u+1) y + avg masas r (F (u+1))
      have eq (y : X) : saldo (record masas step F G u v y) - saldo v = (P y:ℝ) - N y := by
        dsimp [saldo,record,masas,P,N,r]; ring
      simp_rw [eq]; rw [media_sub]
      have e : avg masas r P = avg masas r N := by
        change avg masas r (fun y => masas.add _ _) = avg masas r (fun y => masas.add _ _)
        rw [E2.avg_plus,E2.avg_plus,E2.avg_constant,E2.avg_constant,norm]
        change _ + 1*_ = _ + 1*_ ; ring
      rw [e,sub_self]
    · simp [guarded,onlyOn,hv,point,media,masas]
  · intro u v i mem
    by_cases hv : V v.state
    · simp only [guarded,onlyOn,hv,if_true,row,historyRow,List.mem_map] at mem
      obtain ⟨j,hj,rfl⟩ := mem
      obtain ⟨l,r⟩ := jump u v.state hv j hj
      change (F (u+1) j.2:ℝ) + avg masas _ _ ≤ (G (u+1) j.2:ℝ) + avg masas _ _ + B at l
      change (G (u+1) j.2:ℝ) + avg masas _ _ ≤ (F (u+1) j.2:ℝ) + avg masas _ _ + B at r
      simp only [saldo,record]; change |(_ + (_ + _) - (_ + (_ + _))) - (_ - _)| ≤ _
      have algebra (x y a b c d t : ℝ) (l : a+b ≤ c+d+t) (r : c+d ≤ a+b+t) :
          |(x+(a+b) - (y+(c+d))) - (x-y)| ≤ t := by
        apply abs_le.mpr; constructor <;> linarith
      exact algebra _ _ _ _ _ _ _ l r
    · simp only [guarded,onlyOn,hv,if_false,point,List.mem_singleton] at mem
      subst i; simp
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.libro_centrado
