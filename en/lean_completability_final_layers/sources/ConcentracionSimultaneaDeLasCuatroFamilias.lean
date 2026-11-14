import LasCuatroFamiliasDeMasasRetenidas
import DesviacionBilateralDeLasMasasRetenidas
namespace ArticuloA.Historias
open Repair Limites Real
noncomputable section
open Classical
open scoped BigOperators

theorem union_finita_de_eventos_de_reserva {ι κ : Type} [Fintype ι] [Fintype κ]
    (τ : ℝ) (prob : τ∈Set.Icc (0:ℝ) 1) (E : κ→(ι→Bool)→Prop) (p : ℝ)
    (each : ∀ i,mediaCubo τ (fun u=>if E i u then 1 else 0)≤p) :
    mediaCubo τ (fun u=>if ∃ i,E i u then 1 else 0)≤(Fintype.card κ:ℝ)*p := by
  let flag (i : κ) (u : ι→Bool) : ℝ := if E i u then 1 else 0
  have mono (u : ι→Bool) : (if ∃ i,E i u then (1:ℝ) else 0) ≤ ∑ i : κ,flag i u := by
    by_cases exi : ∃ i,E i u
    · obtain ⟨i,hi⟩:=exi
      rw [if_pos (show ∃ i,E i u from ⟨i,hi⟩),←(show flag i u=1 from if_pos hi)]
      exact Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>flag j u)
        (fun _ _=>by dsimp [flag]; split <;> norm_num) (Finset.mem_univ i)
    · rw [if_neg exi]
      exact Finset.sum_nonneg (fun _ _=>by dsimp [flag]; split <;> norm_num)
  apply (mediaCubo_mono prob mono).trans
  have eq : mediaCubo τ (fun u=>∑ i : κ,flag i u)=∑ i : κ,mediaCubo τ (flag i) := by
    unfold mediaCubo
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [eq]
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each i)

theorem cola_simultanea_de_todas_las_fibras {n} (w : Cell n→ℝ) (B τ t : ℝ)
    (prob : τ∈Set.Icc (0:ℝ) 1) (bp : 0<B) (cap : ∀ e,|w e|≤B)
    (tp : 0≤t) (corte : t≤2*(4*(n:ℝ)+2)*B) :
    mediaCubo τ (fun u=>if ∃ i : FibraDeB1 n,t≤|masaAuxiliar w i u-centroDeLaFibra τ w i| then 1 else 0) ≤
      (6*(n:ℝ)+2)*(2*exp (-(t^2)/(4*(4*(n:ℝ)+2)*B^2))) := by
  let m : ℝ:=4*(n:ℝ)+2
  have hm : m=(Fintype.card (LineaReservable n):ℝ) := by
    simp [m,LineaReservable,Fintype.card_prod]; ring
  have fibers : (Fintype.card (FibraDeB1 n):ℝ)=6*(n:ℝ)+2 := by
    simp [FibraDeB1,LineaReservable,Fintype.card_prod,Fintype.card_sum]; ring
  rw [←fibers]
  apply union_finita_de_eventos_de_reserva τ prob
  intro i
  have h:=cola_bilateral_optimizada prob bp tp m hm (by dsimp [m]; positivity) corte
    (masaAuxiliar w i) (oscilacion_de_cada_fibra w B bp.le cap i)
  rw [media_de_cada_fibra] at h
  exact h

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_simultanea_de_todas_las_fibras
