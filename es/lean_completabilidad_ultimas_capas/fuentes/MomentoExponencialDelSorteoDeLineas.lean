import SeparacionDelPrimerBitDeLaReserva
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators
open Real

theorem dos_valores_centrados {τ B θ a b : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (hθ : 0≤θ) (small : θ*B≤1) (osc : |b-a|≤B) :
    let H:=(1-τ)*a+τ*b
    (1-τ)*exp (θ*(a-H))+τ*exp (θ*(b-H))≤exp ((θ*B)^2) := by
  let H:=(1-τ)*a+τ*b
  have low : |a-H|≤B:=by
    have eq : a-H=τ*(a-b):=by dsimp [H]; ring
    rw [eq,abs_mul,abs_of_nonneg prob.1,abs_sub_comm a b]
    exact (mul_le_mul_of_nonneg_right prob.2 (abs_nonneg _)).trans (by simpa using osc)
  have high : |b-H|≤B:=by
    have eq : b-H=(1-τ)*(b-a):=by dsimp [H]; ring
    rw [eq,abs_mul,abs_of_nonneg (sub_nonneg.mpr prob.2)]
    exact (mul_le_mul_of_nonneg_right (show 1-τ≤1 by linarith only [prob.1]) (abs_nonneg _)).trans (by simpa using osc)
  have maj (y : ℝ) (hy : |y|≤B) : exp (θ*y)≤1+θ*y+(θ*B)^2:=by
    have ab : |θ*y|≤θ*B:=by rw [abs_mul,abs_of_nonneg hθ]; exact mul_le_mul_of_nonneg_left hy hθ
    have sq:=sq_le_sq' (abs_le.mp ab).1 (abs_le.mp ab).2
    have rem:=(le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le (ab.trans small))
    linarith only [rem,sq]
  have lo:=mul_le_mul_of_nonneg_left (maj _ low) (sub_nonneg.mpr prob.2)
  have hi:=mul_le_mul_of_nonneg_left (maj _ high) prob.1
  change (1-τ)*exp (θ*(a-H))+τ*exp (θ*(b-H))≤_
  apply (add_le_add lo hi).trans
  have eq : (1-τ)*(1+θ*(a-H)+(θ*B)^2)+τ*(1+θ*(b-H)+(θ*B)^2)=1+(θ*B)^2:=by dsimp [H]; ring
  rw [eq,add_comm]
  exact Real.add_one_le_exp _

theorem mgf_de_reservas_por_coordenadas {τ B θ : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (hθ : 0≤θ) (small : θ*B≤1) (m : ℕ) (f : (Fin m→Bool)→ℝ) (osc : oscilacionPorBit f B) :
    mediaCubo τ (fun ω=>exp (θ*(f ω-mediaCubo τ f)))≤exp ((m:ℝ)*(θ*B)^2) := by
  induction m with
  | zero=>
    let zero : Fin 0→Bool:=fun _=>false
    have all (ω : Fin 0→Bool) : f ω=f zero:=congrArg f (Subsingleton.elim _ _)
    have ef : mediaCubo τ f=f zero:=by
      rw [show f=(fun _=>f zero) from funext all,mediaCubo_const]
    have neutral (ω : Fin 0→Bool) : exp (θ*(f ω-mediaCubo τ f))=1:=by rw [ef,all ω,sub_self,mul_zero,Real.exp_zero]
    simp_rw [neutral]
    simp [mediaCubo_const]
  | succ m ih=>
    let F (b : Bool) (v : Fin m→Bool):=f (Fin.cons b v)
    let H (b : Bool):=mediaCubo τ (F b)
    let μ:=mediaCubo τ f
    let top:=exp ((m:ℝ)*(θ*B)^2)
    have each (b : Bool) : mediaCubo τ (fun v=>exp (θ*(F b v-μ)))≤top*exp (θ*(H b-μ)):=by
      have o : oscilacionPorBit (F b) B:=by
        intro i v u away
        apply osc i.succ
        intro j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro s ne
          simpa using away s (fun eq=>ne (congrArg Fin.succ eq))
      have hop (v) : exp (θ*(F b v-μ))=exp (θ*(F b v-H b))*exp (θ*(H b-μ)):=by
        rw [←Real.exp_add]; congr 1; ring
      simp_rw [hop]
      rw [mediaCubo_mul_const]
      exact mul_le_mul_of_nonneg_right (ih _ o) (Real.exp_pos _).le
    have between := rango_de_medias_al_revelar τ B prob f osc
    have two := dos_valores_centrados prob hθ small between
    have id : μ=(1-τ)*H false+τ*H true:=mediaCubo_cons τ f
    change (1-τ)*exp (θ*(H false-_))+τ*exp (θ*(H true-_))≤_ at two
    rw [←id] at two
    change mediaCubo τ (fun ω=>exp (θ*(f ω-μ)))≤_
    rw [mediaCubo_cons]
    apply (add_le_add (mul_le_mul_of_nonneg_left (each false) (sub_nonneg.mpr prob.2))
      (mul_le_mul_of_nonneg_left (each true) prob.1)).trans
    calc
      _ = top*((1-τ)*exp (θ*(H false-μ))+τ*exp (θ*(H true-μ))) := by ring
      _ ≤ top*exp ((θ*B)^2) := mul_le_mul_of_nonneg_left two (Real.exp_pos _).le
      _ = _ := by dsimp [top]; rw [←Real.exp_add,Nat.cast_succ]; congr 1; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_valores_centrados
#print axioms ArticuloA.Historias.mgf_de_reservas_por_coordenadas
