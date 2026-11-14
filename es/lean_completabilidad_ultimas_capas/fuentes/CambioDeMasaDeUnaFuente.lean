import SumaEnUnaLineaDelTablero
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem distancia_entre_banderas (P Q : Prop) :
    |estadoEscalar P-estadoEscalar Q|≤1 := by
  by_cases a:P <;> by_cases b:Q <;> simp [estadoEscalar,indicator,a,b]

private theorem acotar_por_lineas {n} (X : State n) (a : Choice n) (e : Cell n) :
    |estadoEscalar (estadoFuente (next X a) e false)-estadoEscalar (estadoFuente X e false)|≤
      ∑ i : Fin 4,estadoEscalar (lines e i=lineOf a i) := by
  have non (i : Fin 4) := escalar_no_negativo (lines e i=lineOf a i)
  by_cases eq : ∃ i,consumeVertex a i (lines e i)
  · obtain ⟨i,hit⟩:=eq
    have hi:=consumed_eq a i _ hit
    have one : estadoEscalar (lines e i=lineOf a i)=1 := by simp [estadoEscalar,indicator,hi]
    exact (distancia_entre_banderas _ _).trans (one ▸
      Finset.single_le_sum (f:=fun j : Fin 4 => estadoEscalar (lines e j=lineOf a j))
        (fun j _ => non j) (Finset.mem_univ i))
  · have same : estadoFuente (next X a) e false ↔ estadoFuente X e false :=
      (available_after X a e).trans ⟨And.left,fun h => ⟨h,fun i yes => eq ⟨i,yes⟩⟩⟩
    rw [propext same,sub_self,abs_zero]; exact Finset.sum_nonneg (fun i _ => non i)

theorem cambio_total_de_fuente {n} (hn : 0<n) (X : State n) (a : Choice n) (fresh : admissible X a) (o : Bool) :
    (∑ e : Cell n,|masaFuente (next X a) o e-masaFuente X o e|)≤4 := by
  cases o
  · have cap (e : Cell n) := acotar_por_lineas X a e
    have size : (∑ e : Cell n,∑ i : Fin 4,estadoEscalar (lines e i=lineOf a i))≤4*(n:ℝ) := by
      rw [Finset.sum_comm]
      simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
        masa_de_una_linea (n:=n) i (lineOf a i))
    have pos : (0:ℝ)<n := by exact_mod_cast hn
    simp only [masaFuente,←mul_sub,abs_mul,abs_of_nonneg (NNReal.coe_nonneg _),←Finset.mul_sum]
    simp only [pesoDeUnaFuente,Bool.false_eq_true,if_false,NNReal.coe_inv,NNReal.coe_natCast]
    exact (mul_le_mul_of_nonneg_left ((Finset.sum_le_sum (fun e _ => cap e)).trans size)
      (inv_nonneg.mpr pos.le)).trans_eq (by field_simp)
  · cases a with
    | fail => simp [masaFuente,estadoFuente,next]
    | virtual _ => simp [masaFuente,estadoFuente,next]
    | real g =>
      have per (e : Cell n) :
          |masaFuente (next X (.real g)) true e-masaFuente X true e|≤estadoEscalar (e=g) := by
        by_cases eq:e=g
        · simp [masaFuente,pesoDeUnaFuente,eq,estadoEscalar,indicator]; split <;> split <;> norm_num
        · have same : estadoFuente (next X (.real g)) e true ↔ estadoFuente X e true := by
            simpa only [estadoFuente,if_true,next,eq,false_or] using (ArticuloA.Repair.inserted X.physical g fresh e)
          simp only [masaFuente,propext same,sub_self,abs_zero]
          exact escalar_no_negativo _
      exact ((Finset.sum_le_sum (fun e _ => per e)).trans (suma_indicador_unico
        (fun e : Cell n => e=g) (fun _ _ i j => i.trans j.symm))).trans (by norm_num)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.distancia_entre_banderas
#print axioms ArticuloA.Historias.cambio_total_de_fuente
