import EntropiaDelNucleoFisico
import PasosPositivosDeUnaHistoria
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel Trayectoria.E2 RealFinita Corte
noncomputable section
open Classical

theorem proyectar_ultimo_estado {X : Type} (S : ℕ→X→Atoms ℝ≥0 X) (t T : ℕ) (x : X) (f : X→ℝ≥0) :
    avg masas (rutas S t T x) (fun l => f (estadoEn x l T))=avg masas (leaves masas S t T x) f := by
  induction T generalizing x t with
  | zero => rw [rutas,leaves,avg_point,avg_point]; rfl
  | succ T ih =>
    rw [rutas,leaves,avg_bind,avg_bind]; apply congrArg (avg masas _); funext y
    rw [avg_push]; exact ih (t+1) y

private theorem suma_por_tableros {n q} (R : Atoms ℝ≥0 (State n)) (P : Tablero n q→Prop) :
    ∑ b : Tablero n q,(if P b then (avg masas R (indicadorExitoso b.val)).val else 0) =
    (avg masas R (fun x => if esExito x ∧ ∃ b : Tablero n q,P b ∧ x.physical=b.val then 1 else 0)).val := by
  let w (x : State n) (b : Tablero n q) : ℝ := if P b then (indicadorExitoso b.val x:ℝ) else 0
  let g (x : State n) : ℝ≥0 := if esExito x ∧ ∃ b : Tablero n q,P b ∧ x.physical=b.val then 1 else 0
  have pt (x : State n) : ∑ b,w x b=(g x:ℝ) := by
    by_cases hit : esExito x ∧ ∃ b : Tablero n q,P b ∧ x.physical=b.val
    · obtain ⟨b,pb,xb⟩:=hit.2
      rw [Finset.sum_eq_single b]
      · change (if P b then (indicadorExitoso b.val x:ℝ) else 0)=_
        rw [if_pos pb]; simp [indicadorExitoso,g,hit,hit.1.1,hit.1.2.1,hit.1.2.2,xb,pb]
      · intro j _ ne
        have diff : x.physical≠j.val := fun eq => ne (Subtype.ext (eq.symm.trans xb))
        simp [w,indicadorExitoso,diff]
      · simp
    · rw [show g x=0 by exact if_neg hit]
      simp only [NNReal.coe_zero]
      apply Finset.sum_eq_zero; intro b _
      by_cases pb : P b
      · have miss : ¬(x.failed=false ∧ x.reals=0 ∧ x.virtuals=0 ∧ x.physical=b.val) := fun t =>
          hit ⟨⟨t.1,t.2.1,t.2.2.1⟩,b,pb,t.2.2.2⟩
        simp [w,pb,indicadorExitoso,miss]
      · simp [w,pb]
  induction R with
  | nil => simp [avg,MassScale.sum,masas]
  | cons i R ih =>
    let rem (b : Tablero n q) : ℝ := if P b then (avg masas R (indicadorExitoso b.val)).val else 0
    have split (b : Tablero n q) : (if P b then (avg masas (i::R) (indicadorExitoso b.val)).val else 0) =
        (i.1:ℝ)*w i.2 b+rem b := by
      by_cases pb : P b
      · rw [if_pos pb]; simp [w,rem,pb]; rfl
      · simp [pb,w,rem]
    simp_rw [split]; rw [Finset.sum_add_distrib,←Finset.mul_sum,pt]
    change (i.1:ℝ)*(g i.2:ℝ)+∑ b,rem b=_
    rw [show (∑ b,rem b)=((avg masas R g:ℝ≥0):ℝ) from ih]
    rfl

theorem suma_de_masas_condicionables {n q h} (u : ColorWeights ℝ≥0) (P : Tablero n q→Prop)
    (F : State n→Prop) (implies : ∀ x,esExito x → ∀ b : Tablero n q,P b → x.physical=b.val → F x) :
    ∑ b : Tablero n q,(if P b then masaTablero b h u else 0)≤
      (avg masas (terminalE2 n h u) (mark masas F)).val := by
  rw [show (∑ b : Tablero n q,if P b then masaTablero b h u else 0)=_ from
    suma_por_tableros (terminalE2 n h u) P]
  apply NNReal.coe_le_coe.mpr
  apply avg_mono; intro a _
  split
  · rename_i hit
    obtain ⟨b,pb,eq⟩:=hit.2
    rw [mark,if_pos (implies _ hit.1 b pb eq)]; exact le_rfl
  · exact zero_le _

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_de_masas_condicionables
