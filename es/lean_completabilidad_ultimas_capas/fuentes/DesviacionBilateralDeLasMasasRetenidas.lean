import OscilacionDelPesoDeUnaFibra
namespace ArticuloA.Historias
open Repair Limites Real
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type} [Fintype ι]

theorem cola_superior_del_cubo {τ B θ t : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (hθ : 0≤θ) (small : θ*B≤1) (f : (ι→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    mediaCubo τ (fun u=>if t≤f u-mediaCubo τ f then 1 else 0) ≤
      exp ((Fintype.card ι:ℝ)*(θ*B)^2-θ*t) := by
  let ind (u : ι→Bool) : ℝ:=if t≤f u-mediaCubo τ f then 1 else 0
  have pointw (u) : ind u*exp (θ*t)≤exp (θ*(f u-mediaCubo τ f)) := by
    by_cases ht : t≤f u-mediaCubo τ f
    · simp only [ind,if_pos ht,one_mul,Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left ht hθ
    · simp [ind,ht,(Real.exp_pos _).le]
  have a:=mediaCubo_mono prob pointw
  rw [mediaCubo_mul_const] at a
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (a.trans (mgf_de_reservas prob hθ small f osc))

theorem cola_bilateral_del_cubo {τ B θ t : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (hθ : 0≤θ) (small : θ*B≤1) (f : (ι→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    mediaCubo τ (fun u=>if t≤|f u-mediaCubo τ f| then 1 else 0) ≤
      2*exp ((Fintype.card ι:ℝ)*(θ*B)^2-θ*t) := by
  let g (u : ι→Bool):=f u*(-1)
  have sg : mediaCubo τ g= -(mediaCubo τ f):=by simpa [g] using (mediaCubo_mul_const τ (-1) f)
  have og : oscilacionPorBit g B:=by
    intro j u v h
    simpa [g,abs_sub_comm,sub_eq_add_neg,add_comm] using osc j v u (fun i ne=>(h i ne).symm)
  let plus (u : ι→Bool) : ℝ := if t≤f u-mediaCubo τ f then 1 else 0
  let minus (u : ι→Bool) : ℝ := if t≤g u-mediaCubo τ g then 1 else 0
  have both (u : ι→Bool) : (if t≤|f u-mediaCubo τ f| then (1:ℝ) else 0) ≤ plus u+minus u := by
    have eq : g u-mediaCubo τ g= -(f u-mediaCubo τ f) := by rw [sg]; dsimp [g]; ring
    by_cases pos : 0≤f u-mediaCubo τ f
    · rw [abs_of_nonneg pos]
      unfold plus minus
      split_ifs <;> norm_num
    · rw [abs_of_neg (lt_of_not_ge pos)]
      unfold plus minus
      rw [eq]
      split_ifs <;> norm_num
  have a:=mediaCubo_mono prob both
  have split : mediaCubo τ (fun u=>plus u+minus u)=mediaCubo τ plus+mediaCubo τ minus:=by
    simp [mediaCubo,mul_add,Finset.sum_add_distrib]
  rw [split] at a
  exact a.trans ((add_le_add (cola_superior_del_cubo prob hθ small f osc)
    (cola_superior_del_cubo prob hθ small g og)).trans_eq (two_mul _).symm)

theorem cola_bilateral_optimizada {τ B t : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (bp : 0<B) (tp : 0≤t) (m : ℝ) (hm : m=Fintype.card ι) (mp : 0<m)
    (corte : t≤2*m*B) (f : (ι→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    mediaCubo τ (fun u=>if t≤|f u-mediaCubo τ f| then 1 else 0) ≤ 2*exp (-(t^2)/(4*m*B^2)) := by
  let θ:=t/(2*m*B^2)
  have qp : 0<2*m*B^2 := by positivity
  have hθ : 0≤θ := div_nonneg tp qp.le
  have small : θ*B≤1 := by
    dsimp [θ]
    rw [div_mul_eq_mul_div,div_le_iff₀ qp]
    nlinarith only [mul_le_mul_of_nonneg_right corte bp.le]
  have bound:=cola_bilateral_del_cubo (t:=t) prob hθ small f osc
  rw [←hm] at bound
  have eq : m*(θ*B)^2-θ*t= -(t^2)/(4*m*B^2) := by
    dsimp [θ]
    field_simp [mp.ne',bp.ne']
    ring
  rwa [eq] at bound

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_bilateral_optimizada
