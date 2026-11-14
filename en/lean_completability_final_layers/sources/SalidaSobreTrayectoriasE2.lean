import Mathlib.Algebra.BigOperators.Fin
import InnovacionBilateralDeE2
open scoped BigOperators NNReal
namespace ArticuloA.RealFinita
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
open Classical
private theorem masa_por_indices {X : Type} (l : Atoms ℝ≥0 X) (b : X→Prop) :
    (∑ i : Fin l.length,if b l[i.val].2 then l[i.val].1.val else 0) =
      (avg masas l (mark masas b)).val := by
  induction l with
  | nil => simp [avg,masas,Corte.MassScale.sum]
  | cons x l ih =>
    change (∑ i : Fin (l.length+1),if b (x::l)[i.val].2 then (x::l)[i.val].1.val else 0)=_
    rw [Fin.sum_univ_succ]
    change (if b x.2 then x.1.val else 0)+(∑ i : Fin l.length,_) =
      x.1.val*(mark masas b x.2).val+(avg masas l _).val
    rw [←ih]; by_cases yes : b x.2 <;> simp [mark,yes,masas]

def limiteSalto (M H : ℝ≥0) : ℝ := 2*(1+4*M.val+H.val)

theorem capacidad_uniforme (M H : ℝ≥0) (c : Coord) : 2*(coordCap masas M H c).val≤limiteSalto M H := by
  have m0 : 0≤M.val := M.property; have h0 : 0≤H.val := H.property
  cases c <;> simp [coordCap,MassScale.times,masas,limiteSalto] <;> change 0 ≤ (M:ℝ) at m0 <;> change 0 ≤ (H:ℝ) at h0 <;> linarith

theorem salida_con_testigo {n : ℕ} (hn : n≠0) (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0)
    (halt : ℕ→State n→Bool) (x : ℕ×State n) (T : ℕ) (M H : ℝ≥0) (cap : ∀ e,v e≤M)
    (line : ∀ t (y : State n),halt t y=false → ∀ f j,j<2*n-1 → y.active f j → w f j≤H)
    (θ g : ℝ) (tp : 0≤θ) (small : θ*limiteSalto M H≤1) (bad : List (ℕ×State n)→Prop)
    (witness : ∀ atom∈rutas (pasoParado w halt) 0 T x,bad atom.2 →
      ∃ c : Activa n,∃ t≤T,g < |ruidoE2 v w halt x (coordenada c) t atom.2|) :
    (avg masas (rutas (pasoParado w halt) 0 T x) (mark masas bad)).val ≤
      (6+4*(↑(2*n-1):ℝ))*(T+1)*(2*Real.exp (T*(θ*limiteSalto M H)^2-θ*g)) := by
  let L:=rutas (pasoParado w halt) 0 T x
  let B:=limiteSalto M H
  let r:=fun (i : Fin L.length) (c : Activa n) (t : ℕ) => ruidoE2 v w halt x (coordenada c) t L[i.val].2
  have tails (c : Activa n) (t : ℕ) (ht : t≤T) :
      (∑ i : Fin L.length,if g < |r i c t| then L[i.val].1.val else 0) ≤ 2*Real.exp (T*(θ*B)^2-θ*g) := by
    let F := fun l => ruidoE2 v w halt x (coordenada c) t l
    have b := capacidad_uniforme M H (coordenada c)
    have a := mul_le_mul_of_nonneg_left b tp
    have core := cola_fisica_en_prefijo hn v w halt (coordenada c) M H cap line x t T ht θ g tp (a.trans small)
    calc
      _ ≤ ∑ i : Fin L.length, if g ≤ |F L[i.val].2| then L[i.val].1.val else 0 := by
        apply Finset.sum_le_sum; intro i _
        by_cases hit : g < |F L[i.val].2|
        · simp [r,F] at hit ⊢; simp [hit,hit.le]
        · change (if g < |F L[i.val].2| then _ else _)≤_
          rw [if_neg hit]; split
          · exact L[i.val].1.property
          · exact le_rfl
      _ = _ := masa_por_indices L (fun l => g ≤ |F l|)
      _ ≤ _ := core
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr; apply sub_le_sub_right
        exact mul_le_mul (Nat.cast_le.mpr ht) (pow_le_pow_left₀ (mul_nonneg tp (mul_nonneg (by norm_num) (coordCap masas M H (coordenada c)).property)) a 2) (sq_nonneg _) (Nat.cast_nonneg _)
  have bound := Seguimiento.masa_de_salida (Finset.univ : Finset (Fin L.length)) (fun i => L[i.val].1.val)
    (fun i _ => L[i.val].1.property) (fun i => bad L[i.val].2) r T g _
    (fun i _ h => witness _ (List.getElem_mem i.isLt) h) tails
  rw [masa_por_indices] at bound
  simpa only [Activa,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    show (2:ℝ)+4=6 by norm_num] using bound
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.salida_con_testigo
