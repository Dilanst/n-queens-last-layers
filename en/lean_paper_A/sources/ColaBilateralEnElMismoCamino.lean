import PrefijosDeUnaMismaTrayectoria
open scoped NNReal
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel Trayectoria.Adjunto Corte
noncomputable section
open Classical
variable {X : Type}
def libroCero (x : X) : HistoryBook X ℝ≥0 := ⟨x,0,0,0,0⟩

theorem cola_de_prefijo (step : ℕ→X→Atoms ℝ≥0 X) (F G : ℕ→X→ℝ≥0)
    (norm : ∀ t x,total masas (step t x)=1) (B : ℝ≥0) (V : X→Prop)
    (inv : ∀ t x,V x → ∀ i∈step t x,V i.2)
    (jump : ∀ t x,V x → ∀ i∈step t x,within masas
      (F (t+1) i.2+avg masas (step t x) (G (t+1)))
      (G (t+1) i.2+avg masas (step t x) (F (t+1))) B)
    (t m k : ℕ) (le : m≤k) (x : X) (vx : V x) (θ a : ℝ) (tp : 0≤θ) (small : θ*B≤1) :
    (avg masas (rutas step t k x) (mark masas (fun l =>
      a≤|saldo (leerLibro step F G t (libroCero x) (l.take m))|))).val ≤
        2*Real.exp ((m:ℝ)*(θ*B)^2-θ*a) := by
  let L := rutas step t k x
  let hi := fun l : List X => leerLibro step F G t (libroCero x) (l.take m)
  let lo := fun l : List X => leerLibro step G F t (libroCero x) (l.take m)
  have flip (l : List X) : saldo (lo l) = -saldo (hi l) := by
    have q := libro_invertido step F G (l.take m) t (libroCero x)
    exact (congrArg saldo q).trans (saldo_invertido _)
  have h0 : saldo (libroCero x)=0 := by simp [saldo,libroCero]
  have up := cola_libro realExp step F G norm B V inv jump t m (libroCero x) vx θ a tp small
  have down := cola_libro realExp step G F norm B V inv
    (fun t x v i h => ⟨(jump t x v i h).2,(jump t x v i h).1⟩) t m (libroCero x) vx θ a tp small
  rw [←proyeccion_de_prefijo step norm F G t m k le] at up
  rw [←proyeccion_de_prefijo step norm G F t m k le] at down
  let good := fun l : List X => mark masas (fun y => a≤saldo (hi y)) l
  let opp := fun l : List X => mark masas (fun y => a≤saldo (lo y)) l
  have two : avg masas L (mark masas (fun l => a≤|saldo (hi l)|)) ≤ avg masas L good + avg masas L opp := by
    change _ ≤ masas.add _ _
    rw [←avg_plus]
    apply avg_mono masas L
    intro i _
    simp only [good,opp,mark]
    by_cases pos : a≤saldo (hi i.2)
    · simp only [pos,if_true]; split <;> change _≤(1:ℝ≥0)+_ <;> first | exact le_add_of_nonneg_right (zero_le _) | exact zero_le _
    · by_cases neg : a≤saldo (lo i.2)
      · simp only [pos,neg,if_false,if_true]; split <;> change _≤(0:ℝ≥0)+1 <;> norm_num [masas]
      · have no : ¬a≤|saldo (hi i.2)| := by
          by_cases hs : 0≤saldo (hi i.2)
          · rwa [abs_of_nonneg hs]
          · rw [abs_of_neg (lt_of_not_ge hs),←flip]; exact neg
        simp only [pos,neg,no,if_false]; exact zero_le _
  have tR : _ ≤ (avg masas L good).val + (avg masas L opp).val := NNReal.coe_le_coe.mpr two
  change (avg masas L good).val ≤ realExp.fn _ at up
  change (avg masas L opp).val ≤ realExp.fn _ at down
  simp only [h0,mul_zero,add_zero,realExp] at up down
  exact tR.trans (by linarith only [up,down])
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola_de_prefijo
