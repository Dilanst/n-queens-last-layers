import SumaDeLosUsosDeLineaSinDuplicarFibras
import PerdidaDeEntropiaDeUnaDensidadReservada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem suma_de_todas_las_masas_del_tablero {n q : ℕ} (v : Cell n→ℝ≥0) (mass : (∑ e,(v e:ℝ))=q) :
    (∑ j : FibraDeB1 n,masaBajo (fun e=>(v e:ℝ)) (enLaFibra j))=4*(q:ℝ) := by
  have a:=suma_de_las_cargas_por_incidencia (fun e=>(v e:ℝ)) (fun _=>(1:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one,←Finset.sum_mul,mass] at a
  linarith only [a]

theorem lineas_integradas_con_error_total {n q : ℕ} (qp : 0<q) (v : Cell n→ℝ≥0)
    (mass : (∑ e,(v e:ℝ))=q) (use : ℕ→FibraDeB1 n→ℝ) {η H b : ℝ}
    (hp : 0<η) (hn : 0≤H) (b1 : 1≤b)
    (margin : ∀ j,masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)≤1-η)
    (bd : ∀ j t,t<q→
      let m:=masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)
      use t j≤b*(m/q+H*(1-(t:ℝ)/q*m))) :
    entropiaLineas (fun e=>(v e:ℝ))-4*q-4*q*((b-1)+b*H*q)/η≤
      ∑ t∈Finset.range q,∑ j : FibraDeB1 n,
        use t j*log (1-(t:ℝ)/q*masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)) := by
  let m (j : FibraDeB1 n):=masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)
  have tot : (∑ j,m j)=4*(q:ℝ):=suma_de_todas_las_masas_del_tablero v mass
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have bn : 0≤b-1:=by linarith only [b1]
  have pos j : 0≤m j:=Finset.sum_nonneg (fun e _=>by dsimp [pesoCuando]; split <;> positivity)
  have per j : aporteCelda (1-m j)-m j-((b-1)+b*H*q)/η*m j≤
      ∑ t∈Finset.range q,use t j*log (1-(t:ℝ)/q*m j):=by
    have a:=integral_discreta_de_cada_fibra qp hp (pos j) (margin j) hn b1 (fun t=>use t j) (bd j)
    have me : m j≤1:=(margin j).trans (by linarith)
    have prod:=mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (pos j) me) bn
    have cost : ((b-1)*m j/q+b*H)*(q*(m j/η))≤((b-1)+b*H*q)/η*m j:=by
      calc _ = ((b-1)*(m j*m j)+(b*H*q)*m j)/η:=by field_simp; ring
           _ ≤ ((b-1)*m j+(b*H*q)*m j)/η:=div_le_div_of_nonneg_right (add_le_add_right prod _) hp.le
           _ = _:=by ring
    exact (sub_le_sub_left cost _).trans a
  have s:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>per j)
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,tot,Finset.sum_comm] at s
  change (∑ j,aporteCelda (1-m j))-4*q-4*q*((b-1)+b*H*q)/η≤_
  convert s using 1; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.lineas_integradas_con_error_total
