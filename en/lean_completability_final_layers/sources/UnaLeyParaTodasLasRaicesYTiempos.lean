import AcuerdoDeLeyesEnLosPrefijos
import ErrorDelGeneradorPorRaiz
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

theorem probabilidad_del_prefijo {X : Type} (S : ℕ→X→Atoms ℝ≥0 X) (norm : ∀ t x,total masas (S t x)=1)
    (g : List X→ℝ≥0) (x : X) (t j T : ℕ) (jt : j≤T) :
    avg masas (rutas S t T x) (fun l => g (l.take j))=avg masas (rutas S t j x) g := by
  induction j generalizing t T x g with
  | zero =>
    simp only [List.take_zero,rutas,avg_point,avg_constant,masa_de_rutas S norm]; exact one_mul _
  | succ j ih =>
    cases T with
    | zero => omega
    | succ T =>
      rw [rutas,rutas,avg_bind,avg_bind]; apply congrArg (avg masas _); funext y
      rw [avg_push,avg_push]; simp only [List.take_succ_cons]
      exact ih (fun l => g (y::l)) y (t+1) T (by omega)

private theorem masa_de_evento {X : Type} (R : Atoms ℝ≥0 X) (P : X→Prop) :
    masas.mass R Prod.fst (fun i => P i.2)=avg masas R (mark masas P) := by
  unfold MassScale.mass avg; apply congrArg (masas.sum R); funext i
  by_cases h : P i.2 <;> simp [mark,h,masas]

theorem union_de_raices_y_horizontes {X : Type} (n T : ℕ) (x : X) (S : ℕ→X→Atoms ℝ≥0 X)
    (norm : ∀ t y,total masas (S t y)=1) (event : Cell n→ℕ→List X→Prop) (b : ℝ≥0)
    (each : ∀ z j,j≤T → avg masas (rutas S 0 j x) (mark masas (event z j))≤b) :
    avg masas (rutas S 0 T x) (mark masas (fun l => ∃ z,∃ j≤T,event z j (l.take j))) ≤
      (n:ℝ≥0)^2*(T+1)*b := by
  let keys := (board n).flatMap (fun z => (List.range (T+1)).map (fun j => (z,j)))
  let R:=rutas S 0 T x
  let E:=fun (a : Cell n×ℕ) (i : ℝ≥0×List X) => event a.1 a.2 (i.2.take a.2)
  have memK (a : Cell n×ℕ) : a∈keys ↔ a.2≤T := by
    rcases a with ⟨z,j⟩; simp [keys,board_complete,Nat.lt_succ_iff]
  have bounds (a) (am : a∈keys) : masas.le (masas.mass R Prod.fst (E a)) b := by
    change masas.mass R Prod.fst (fun i => event a.1 a.2 (i.2.take a.2))≤_
    rw [masa_de_evento R (fun l => event a.1 a.2 (l.take a.2))]; exact (le_of_eq (probabilidad_del_prefijo S norm (mark masas (event a.1 a.2)) x 0 a.2 T
      ((memK a).mp am))).trans (each _ _ ((memK a).mp am))
  have union:=masas.union_budget R Prod.fst keys E b bounds
  have subset:=masas.mass_mono R Prod.fst (P:=fun i => ∃ z,∃ j≤T,event z j (i.2.take j))
    (Q:=fun i => ∃ a∈keys,E a i) (by rintro i ⟨z,j,jt,yes⟩; exact ⟨(z,j),(memK _).mpr jt,yes⟩)
  rw [masa_de_evento R (fun l => ∃ z,∃ j≤T,event z j (l.take j))] at subset
  have len (l : List (Cell n)) : (l.flatMap (fun z => (List.range (T+1)).map (fun j => (z,j)))).length=l.length*(T+1) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  have klen:=len (board n); rw [board_card] at klen
  have cap:=masas.trans subset union
  change _≤masas.times keys.length b at cap
  rw [show keys.length=n*n*(T+1) from klen,times_m,ns_real] at cap
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_two] using cap

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.union_de_raices_y_horizontes
