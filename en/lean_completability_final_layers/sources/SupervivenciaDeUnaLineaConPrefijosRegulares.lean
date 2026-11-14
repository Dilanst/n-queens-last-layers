import InnovacionYDerivaHastaUnaObservacionReal
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
variable {X : Type}

def caminoVivo (guard : ℕ→X→Prop) (live : X→Prop) (t : ℕ) (x : X) : List X→Prop
  | []=>live x
  | y::l=>guard t x ∧ live x ∧ caminoVivo guard live (t+1) y l

theorem producto_de_supervivencia_con_parada (P : ℕ→X→Atoms ℝ≥0 X) (guard : ℕ→X→Prop)
    (live : X→Prop) (b : ℕ→ℝ≥0) (t m : ℕ) (x : X)
    (rate : ∀ s,t≤s→s<t+m→∀ z,guard s z→live z→avg masas (P s z) (mark masas live)≤b s) :
    avg masas (rutas P t m x) (mark masas (caminoVivo guard live t x))≤
      mark masas live x*∏ j∈Finset.range m,b (t+j) := by
  induction m generalizing t x with
  | zero=>rw [rutas,avg_point,Finset.prod_range_zero,mul_one]; change (if live x then (1:ℝ≥0) else 0)≤_; exact le_rfl
  | succ m ih=>
    rw [rutas,avg_bind,Finset.prod_range_succ']
    let W:=∏ j∈Finset.range m,b (t+1+j)
    have eq (j : ℕ) : t+(j+1)=t+1+j:=by omega
    have shift : (∏ j∈Finset.range m,b (t+(j+1)))=W:=by
      apply Finset.prod_congr rfl
      intro j _; rw [eq j]
    rw [shift,Nat.add_zero]
    by_cases safe : guard t x ∧ live x
    · have next y : avg masas ((rutas P (t+1) m y).map (fun i=>(i.1,y::i.2)))
          (mark masas (caminoVivo guard live t x))≤masas.mul W (mark masas live y):=by
        rw [avg_push masas _ (List.cons y)]
        have g : (fun l=>mark masas (caminoVivo guard live t x) (y::l))=mark masas (caminoVivo guard live (t+1) y):=by
          funext l; simp [mark,caminoVivo,safe.1,safe.2]
        rw [g]
        exact (ih (t+1) y (fun s a z=>rate s (by omega) (by omega))).trans_eq (mul_comm _ _)
      apply (avg_mono masas (P t x) _ (fun y=>masas.mul W (mark masas live y)) (fun i _=>next i.2)).trans
      rw [avg_mul]
      have h:=mul_le_mul_of_nonneg_left (rate t le_rfl (by omega) x safe.1 safe.2) (zero_le W)
      simpa [mark,safe.2,masas,W,mul_comm] using h
    · have z y : avg masas ((rutas P (t+1) m y).map (fun i=>(i.1,y::i.2))) (mark masas (caminoVivo guard live t x))=0:=by
        rw [avg_push masas _ (List.cons y)]
        have g : (fun l=>mark masas (caminoVivo guard live t x) (y::l))=fun _=>0:=by
          funext l
          by_cases yes : caminoVivo guard live t x (y::l)
          · exact False.elim (safe ⟨yes.1,yes.2.1⟩)
          · simp [mark,yes,masas]
        rw [g,E2.avg_constant]; exact mul_zero _
      simp_rw [z]
      rw [E2.avg_constant]
      exact (mul_zero _).le.trans (zero_le _)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.producto_de_supervivencia_con_parada
