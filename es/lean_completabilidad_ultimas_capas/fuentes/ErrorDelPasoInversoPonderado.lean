import ComparacionFisicaConElGeneradorIdeal
import MayoranteDelGeneradorEnParejasCompatibles
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def errorDeDeriva {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (t : CuatroMarcas) (u : Mark n) : ℝ :=
  let U:=fun Y => patronInverso Y u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2
  (↑(meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (U (next X a)))):ℝ)-(indicator (U X):ℝ)-
    operadorInverso X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2
      (fun e => (↑(A.birth e/(n:ℝ≥0)^2):ℝ)) (fun v b => (intensidadIdeal A v b:ℝ))

def impactoMultiple {n} (X : State n) (w : ColorWeights ℝ≥0) (t : CuatroMarcas) (u : Mark n) :=
  meanN masas (choices masas X w (·⁻¹)) (fun a =>
    deathsOn (diez u.1 u.2) (golpeDelPar u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2 a)-1)

theorem cota_del_paso_por_patron {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (coh : coherent X) (run : X.failed=false) (t : CuatroMarcas) (coef : Mark n→ℝ) (W : ℝ)
    (wp : 0≤W) (cap : ∀ u∈paresCompatibles n,|coef u|≤W*(escalaDelPatron n t:ℝ)) :
    |∑ u∈paresCompatibles n,coef u*errorDeDeriva A t u| ≤
      W*((costoDeUnPatron A t.1 t.2.1 t.2.2.1 t.2.2.2:ℝ)+
      (↑(escalaDelPatron n t*masas.sum (soporteInverso X t) (impactoMultiple X w t)):ℝ)) := by
  let s:=escalaDelPatron n t
  let U:=fun u : Mark n => patronInverso X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2
  let V:=fun u => filtrarTasa (U u) (impactoMultiple X w t u:ℝ)
  let R:=fun u : Mark n => costoLocal X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2
    (fun e => (errorDelAtomo A e:ℝ)) (fun v b => (errorDeLinea A v b:ℝ))
  have point (u : Mark n) (hu : u∈paresCompatibles n) : |errorDeDeriva A t u|≤R u+V u := by
    have ok:=(Finset.mem_filter.mp hu).2
    have base:=comparar_deriva_con_ideal A u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2 ok coh run
    let row:=choices masas X w (·⁻¹)
    let d:=fun a => deathsOn (diez u.1 u.2) (golpeDelPar u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2 a)-1
    change |errorDeDeriva A t u|≤R u+(↑(meanN masas row (fun a => indicator (U u)*d a)):ℝ) at base
    by_cases yes : U u
    · simpa [V,filtrarTasa,yes,indicator,impactoMultiple,row,d] using base
    · simpa [V,filtrarTasa,yes,indicator,mean_zero,masas] using base
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ u∈paresCompatibles n,W*((s:ℝ)*R u+(s:ℝ)*V u) := by
             apply Finset.sum_le_sum; intro u hu
             rw [abs_mul,←mul_add,←mul_assoc]
             exact mul_le_mul (cap u hu) (point u hu) (abs_nonneg _) (mul_nonneg wp s.property)
       _ = W*((∑ u∈paresCompatibles n,(s:ℝ)*R u)+∑ u∈paresCompatibles n,(s:ℝ)*V u) := by
             rw [←Finset.mul_sum,Finset.sum_add_distrib]
       _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (mayorante_en_parejas A t.1 t.2.1 t.2.2.1 t.2.2.2)
               (cota_de_soporte_ponderada X t.1 t.2.1 t.2.2.1 t.2.2.2 (impactoMultiple X w t) s)) wp

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_del_paso_por_patron
