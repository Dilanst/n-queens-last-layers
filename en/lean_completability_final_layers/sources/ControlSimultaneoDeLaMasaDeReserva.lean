import ConcentracionDeLaMasaMarcadaPorRaiz
import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators Topology
open Real Filter

theorem union_de_cilindros_bajos {n : ℕ} (τ : ℝ) (prob : τ∈Set.Icc (0:ℝ) 1)
    (E : Cell n→(LineaReservable n→Bool)→Prop) (p : ℝ)
    (hr : ∀ z,mediaCubo τ (fun u=>if E z u then 1 else 0)≤p) :
    mediaCubo τ (fun u=>if ∃ z,E z u then 1 else 0)≤(n:ℝ)^2*p := by
  let flag (z : Cell n) (u : LineaReservable n→Bool) : ℝ:=if E z u then 1 else 0
  have mono (u : LineaReservable n→Bool) : (if ∃ z,E z u then (1:ℝ) else 0) ≤ ∑ z : Cell n,flag z u:=by
    by_cases ex : ∃ z,E z u
    · obtain ⟨z,hz⟩:=ex
      rw [if_pos (show ∃ z,E z u from ⟨z,hz⟩)]
      have z1 : flag z u=1:=if_pos hz
      rw [←z1]
      exact Finset.single_le_sum (s:=Finset.univ) (f:=fun z=>flag z u) (fun _ _=>by dsimp [flag]; split <;> norm_num) (Finset.mem_univ z)
    · rw [if_neg ex]
      exact Finset.sum_nonneg (fun _ _=>by dsimp [flag]; split <;> norm_num)
  apply (mediaCubo_mono prob mono).trans
  have id : mediaCubo τ (fun u=>∑ z : Cell n,flag z u) = ∑ z : Cell n,mediaCubo τ (flag z):=by
    unfold mediaCubo
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [id]
  simpa [Cell,pow_two] using Finset.sum_le_sum (s:=Finset.univ) (fun z _=>hr z)

theorem cola_para_todas_las_raices_de_B1 {n : ℕ} (posn : 1≤n) (w : Cell n→ℝ) (pos : ∀ e,0≤w e)
    (rows : ∀ i,masaBajo w (fun e=>e.1=i)≤1) (cols : ∀ i,masaBajo w (fun e=>e.2=i)≤1)
    (diag : ∀ i,masaBajo w (fun e=>i∈lineasPropias e)≤1) (τ q : ℝ)
    (pτ : 0≤τ) (pe : τ≤1/8) (mass : (∑ e : Cell n,w e)=q) (qmin : 4≤q)
    (qmax : q≤n) (half : (n:ℝ)/2≤q) :
    mediaCubo τ (fun u=>if ∃ z,masaMarcadaB1 w z u≤τ^4*q/8 then 1 else 0) ≤
      (n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296) :=
  union_de_cilindros_bajos τ ⟨pτ,by linarith⟩ _ _ (fun z=>
    raiz_con_poca_masa_tiene_cola posn w pos rows cols diag z τ q pτ pe mass qmin qmax half)

theorem cola_de_la_reserva_es_eventualmente_inferior_a_n_menos_cuatro :
    ∀ᶠ n : ℕ in atTop, let τ:=(n:ℝ)^(-exponenteReserva)
      (n:ℝ)^2*exp (-(τ^8)*(n:ℝ)/55296) ≤ 1/(n:ℝ)^4 := by
  let b:=1-8*exponenteReserva
  have bp : 0<b:=by norm_num [b,exponenteReserva]
  have little : Tendsto (fun n : ℕ=>log (n:ℝ)/(n:ℝ)^b) atTop (𝓝 0):=
    (isLittleO_log_rpow_atTop bp).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,little.eventually_lt_const (by norm_num : (0:ℝ)<1/(6*55296))] with n n1 small
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have id : ((n:ℝ)^(-exponenteReserva))^8*(n:ℝ)=(n:ℝ)^b:=by
    rw [←Real.rpow_mul_natCast np.le,←Real.rpow_add_one np.ne']
    congr 1; dsimp [b]; ring
  have s:=(div_lt_iff₀ (Real.rpow_pos_of_pos np b)).mp small
  have exponent : -(((n:ℝ)^(-exponenteReserva))^8)*(n:ℝ)/55296 ≤ -(6*log n):=by
    rw [neg_mul,id]; linarith only [s]
  have ex : exp (-(6*log n))=1/(n:ℝ)^6:=by
    rw [Real.exp_neg,show (6:ℝ)*log n=((6:ℕ):ℝ)*log n by norm_num,Real.exp_nat_mul,Real.exp_log np,one_div]
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent) (sq_nonneg (n:ℝ))).trans
  rw [ex]
  exact le_of_eq (by field_simp; ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_para_todas_las_raices_de_B1
#print axioms ArticuloA.Historias.cola_de_la_reserva_es_eventualmente_inferior_a_n_menos_cuatro
