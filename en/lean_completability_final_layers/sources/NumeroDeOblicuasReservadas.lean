import ConcentracionSimultaneaDeLasCuatroFamilias
namespace ArticuloA.Historias
open Repair Limites Real
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type} [Fintype ι]

def numeroDeReservas (u : ι→Bool) : ℝ := ∑ j : ι,if u j=true then (1:ℝ) else 0

theorem media_del_numero_de_reservas (τ : ℝ) :
    mediaCubo (ι:=ι) τ numeroDeReservas=(Fintype.card ι:ℝ)*τ := by
  unfold mediaCubo numeroDeReservas
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have pointw (j : ι) : (∑ u : ι→Bool,masaDeReserva τ u*(if u j=true then 1 else 0))=τ := by
    have cyl:=probabilidad_de_un_patron_de_reserva τ ({j} : Finset ι) ∅ (by simp)
    simpa [acuerdoDeReserva,mul_ite] using cyl
  calc
    _ = ∑ _j : ι,τ := by
      apply Finset.sum_congr rfl
      intro j _
      exact pointw j
    _ = _ := by simp

theorem cola_del_numero_de_reservas {τ : ℝ} (prob : τ∈Set.Icc (0:ℝ) 1)
    (pos : 0<(Fintype.card ι:ℝ)*τ) :
    mediaCubo (ι:=ι) τ (fun u=>if 2*(Fintype.card ι:ℝ)*τ<numeroDeReservas u then 1 else 0)≤1/2 := by
  let a:=(Fintype.card ι:ℝ)*τ
  let f (u : ι→Bool) : ℝ:= if 2*(Fintype.card ι:ℝ)*τ<numeroDeReservas u then 1 else 0
  have pw (u) : f u*(2*a)≤numeroDeReservas u := by
    by_cases big : 2*(Fintype.card ι:ℝ)*τ<numeroDeReservas u
    · simp only [f,if_pos big,one_mul]
      dsimp [a]; linarith only [big]
    · simp only [f,if_neg big,zero_mul]
      exact Finset.sum_nonneg (fun _ _=> by split <;> norm_num)
  have b:=mediaCubo_mono prob pw
  rw [mediaCubo_mul_const,media_del_numero_de_reservas] at b
  change mediaCubo τ f≤1/2
  have h2 : 0<2*a:=by dsimp [a]; linarith only [pos]
  apply le_of_mul_le_mul_right _ h2
  change mediaCubo τ f*(2*a)≤a at b
  linarith only [b]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_del_numero_de_reservas
#print axioms ArticuloA.Historias.cola_del_numero_de_reservas
