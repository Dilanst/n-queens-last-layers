import LeyIndependienteDeLaReserva
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import ColaExponencialReal
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
open Real

def mediaCubo {ι : Type} [Fintype ι] (τ : ℝ) (f : (ι→Bool)→ℝ) : ℝ :=
  ∑ ω : ι→Bool,masaDeReserva τ ω*f ω

theorem mediaCubo_const {ι : Type} [Fintype ι] (τ v : ℝ) :
    (mediaCubo τ (fun _ : ι→Bool=>v))=v := by
  unfold mediaCubo
  rw [←Finset.sum_mul,normalizacion_de_la_reserva,one_mul]

theorem mediaCubo_mono {ι : Type} [Fintype ι] {τ : ℝ} (p : τ∈Set.Icc (0:ℝ) 1)
    {f g : (ι→Bool)→ℝ} (h : ∀ ω,f ω≤g ω) : mediaCubo τ f≤mediaCubo τ g := by
  exact Finset.sum_le_sum (fun ω _=>mul_le_mul_of_nonneg_left (h ω) (masa_de_reserva_no_negativa τ p ω))

theorem mediaCubo_add_const {ι : Type} [Fintype ι] (τ t : ℝ) (f : (ι→Bool)→ℝ) :
    mediaCubo τ (fun ω=>f ω+t)=mediaCubo τ f+t := by
  simp only [mediaCubo,mul_add,Finset.sum_add_distrib,←Finset.sum_mul,normalizacion_de_la_reserva,one_mul]

theorem mediaCubo_mul_const {ι : Type} [Fintype ι] (τ t : ℝ) (f : (ι→Bool)→ℝ) :
    mediaCubo τ (fun ω=>f ω*t)=mediaCubo τ f*t := by
  simp only [mediaCubo,←mul_assoc,Finset.sum_mul]

theorem mediaCubo_cons {m : ℕ} (τ : ℝ) (f : (Fin (m+1)→Bool)→ℝ) :
    mediaCubo τ f = (1-τ)*mediaCubo τ (fun v=>f (Fin.cons false v))+τ*mediaCubo τ (fun v=>f (Fin.cons true v)) := by
  let eqv:=Fin.consEquiv (fun _ : Fin (m+1)=>Bool)
  let term (ω : Fin (m+1)→Bool):=masaDeReserva τ ω*f ω
  have eq:=Equiv.sum_comp eqv term
  have split (b : Bool) (v : Fin m→Bool) : masaDeReserva τ (Fin.cons b v)=pesoDeBernoulli τ b*masaDeReserva τ v:=by
    simp [masaDeReserva,Fin.prod_univ_succ]
  have initial : mediaCubo τ f=∑ ω : Fin (m+1)→Bool,term ω:=by
    unfold mediaCubo
    apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl
  rw [initial,←eq,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [eqv,Fin.consEquiv,Equiv.coe_fn_mk,term,split,pesoDeBernoulli,mediaCubo,←mul_assoc,Finset.mul_sum]
  simp [mul_assoc,Finset.mul_sum,add_comm]
  congr 1 <;> apply Finset.sum_congr (by ext u; simp) <;> intros <;> rfl

def oscilacionPorBit {ι : Type} (f : (ι→Bool)→ℝ) (B : ℝ) : Prop :=
  ∀ i ω v,(∀ j,j≠i → ω j=v j) → |f ω-f v|≤B

theorem rango_de_medias_al_revelar {m : ℕ} (τ B : ℝ) (p : τ∈Set.Icc (0:ℝ) 1)
    (f : (Fin (m+1)→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    |mediaCubo τ (fun v=>f (Fin.cons true v))-mediaCubo τ (fun v=>f (Fin.cons false v))|≤B := by
  have pt (v : Fin m→Bool) : |f (Fin.cons true v)-f (Fin.cons false v)|≤B:=by
    apply osc 0
    intro j
    refine Fin.cases ?_ ?_ j
    · intro h; exact False.elim (h rfl)
    · intro i _; simp
  apply abs_le.mpr
  constructor
  · have lb:=mediaCubo_mono p (f:=fun v=>f (Fin.cons false v)) (g:=fun v=>f (Fin.cons true v)+B)
       (fun v=>by dsimp only; linarith only [(abs_le.mp (pt v)).1])
    rw [mediaCubo_add_const] at lb
    linarith only [lb]
  · have ub:=mediaCubo_mono p (f:=fun v=>f (Fin.cons true v)) (g:=fun v=>f (Fin.cons false v)+B)
       (fun v=>by dsimp only; linarith only [(abs_le.mp (pt v)).2])
    rw [mediaCubo_add_const] at ub
    linarith only [ub]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.mediaCubo_cons
#print axioms ArticuloA.Historias.rango_de_medias_al_revelar
