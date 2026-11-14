import MomentoExponencialDelSorteoDeLineas
import Mathlib.Data.Fintype.EquivFin
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
open Real
variable {ι κ : Type} [Fintype ι] [Fintype κ]
theorem mediaCubo_transportada (e : ι≃κ) (τ : ℝ) (f : (ι→Bool)→ℝ) :
    mediaCubo τ (fun v : κ→Bool=>f (fun i=>v (e i)))=mediaCubo τ f := by
  let a:=e.symm.arrowCongr (Equiv.refl Bool)
  let term (ω : ι→Bool):=masaDeReserva τ ω*f ω
  have mass (v : κ→Bool) : masaDeReserva τ (a v)=masaDeReserva τ v:=
    e.prod_comp (fun i=>pesoDeBernoulli τ (v i))
  calc
    _ = ∑ u : κ→Bool,term (a u) := by
      unfold mediaCubo
      apply Finset.sum_congr (by ext u; simp)
      intro u _
      unfold term
      rw [mass]
      rfl
    _ = ∑ u : ι→Bool,term u := a.sum_comp term
    _ = _ := by
      unfold mediaCubo
      apply Finset.sum_congr (by ext u; simp)
      intro u _
      rfl

omit [Fintype κ] in
theorem mgf_de_reservas {τ B θ : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1) (hθ : 0≤θ) (small : θ*B≤1)
    (f : (ι→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    mediaCubo τ (fun u=>exp (θ*(f u-mediaCubo τ f)))≤exp ((Fintype.card ι:ℝ)*(θ*B)^2) := by
  let e:=Fintype.equivFin ι
  let f' (v : Fin (Fintype.card ι)→Bool):=f (fun i=>v (e i))
  have os : oscilacionPorBit f' B:=by
    intro i v u h
    apply osc (e.symm i)
    intro l ne
    apply h
    intro eq
    exact ne (e.injective (eq.trans (e.apply_symm_apply i).symm))
  have mg:=mgf_de_reservas_por_coordenadas prob hθ small _ f' os
  have eq : mediaCubo τ f'=mediaCubo τ f:=mediaCubo_transportada e τ f
  rw [eq] at mg
  exact (mediaCubo_transportada e τ (fun u=>exp (θ*(f u-mediaCubo τ f)))).symm.le.trans mg

omit [Fintype κ] in
theorem cola_inferior_para_limite_tres {τ θ t : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1) (hθ : 0≤θ) (small : θ*3≤1)
    (f : (ι→Bool)→ℝ) (osc : oscilacionPorBit f 3) :
    mediaCubo τ (fun ω=>if f ω≤mediaCubo τ f-t then 1 else 0)≤exp ((Fintype.card ι:ℝ)*(θ*3)^2-θ*t) := by
  let g (u : ι→Bool):=f u*(-1)
  have sg : mediaCubo τ g= -(mediaCubo τ f):=by simpa [g] using (mediaCubo_mul_const τ (-1) f)
  have og : oscilacionPorBit g 3:=by
    intro i v u h
    simpa [g,abs_sub_comm,sub_eq_add_neg,add_comm] using osc i u v (fun j ne=>(h j ne).symm)
  have mg := mgf_de_reservas prob hθ small g og
  let ind (u : ι→Bool) : ℝ:=if f u≤mediaCubo τ f-t then 1 else 0
  have pointw (u) : ind u*exp (θ*t)≤exp (θ*(g u-mediaCubo τ g)):=by
    by_cases ht : f u≤mediaCubo τ f-t
    · simp only [ind,if_pos ht,one_mul,Real.exp_le_exp]
      rw [sg]
      change θ*t≤θ*(f u*(-1) - -mediaCubo τ f)
      apply mul_le_mul_of_nonneg_left _ hθ
      linarith only [ht]
    · simp [ind,ht,(Real.exp_pos _).le]
  have chk:=mediaCubo_mono prob pointw
  rw [mediaCubo_mul_const] at chk
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (chk.trans mg)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.mediaCubo_transportada
#print axioms ArticuloA.Historias.mgf_de_reservas
#print axioms ArticuloA.Historias.cola_inferior_para_limite_tres
