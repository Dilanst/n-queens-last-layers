import CambioConjuntoDelPatronInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def marcaDelPar {n} (X : State n) (t : CuatroMarcas) (u : Mark n) :=
  estadoEscalar (patronInverso X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2)
def totalPonderado {n} (X : State n) (c : CuatroMarcas→Mark n→ℝ) :=
  ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,c t u*marcaDelPar X t u

theorem masa_del_patron_antes_del_paso {n} (X : State n) (g : Legal X.physical) (t : CuatroMarcas) :
    ∑ u∈paresCompatibles n,(escalaDelPatron n t:ℝ)*marcaDelPar X t u≤(n:ℝ)^2 := by
  have scale (u : Mark n) : (escalaDelPatron n t:ℝ)*marcaDelPar X t u ≤
      masaFuente X t.1 u.1*masaFuente X t.2.1 u.2 := by
    rw [show (escalaDelPatron n t:ℝ)*marcaDelPar X t u = patronEscalado X t u from
      (identidad_del_patron_escalado X t u).symm]
    exact mul_le_of_le_one_right (mul_nonneg (masaFuente_no_negativa _ _ _) (masaFuente_no_negativa _ _ _))
      (escalar_a_lo_sumo_uno _)
  apply (Finset.sum_le_sum (fun u _ => scale u)).trans
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ =>
    mul_nonneg (masaFuente_no_negativa _ _ _) (masaFuente_no_negativa _ _ _))).trans
  rw [Fintype.sum_prod_type]; simp only [←Finset.mul_sum,←Finset.sum_mul]
  simpa only [sq] using mul_le_mul (masa_total_de_fuente g t.1) (masa_total_de_fuente g t.2.1)
    (Finset.sum_nonneg (fun e _ => masaFuente_no_negativa X _ e)) (Nat.cast_nonneg _)

theorem variacion_del_atomo_completo {n} (hn : 0<n) (X : State n) (a : Choice n) (good : coherent X)
    (live : allowed X a) (W : ℝ) (wp : 0≤W) (c : CuatroMarcas→Mark n→ℝ)
    (cap : ∀ t,∀ u∈paresCompatibles n,|c t u|≤W*(escalaDelPatron n t:ℝ)) :
    ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,|c t u*(marcaDelPar (next X a) t u-marcaDelPar X t u)|≤160*W*n := by
  have each (t : CuatroMarcas) (u : Mark n) (hu : u∈paresCompatibles n) :
      |c t u*(marcaDelPar (next X a) t u-marcaDelPar X t u)|≤
      W*|patronEscalado (next X a) t u-patronEscalado X t u| := by
    simp only [identidad_del_patron_escalado,←mul_sub,abs_mul,abs_of_nonneg (NNReal.coe_nonneg _),←mul_assoc]
    exact mul_le_mul_of_nonneg_right (cap t u hu) (abs_nonneg _)
  have pat (t : CuatroMarcas) :
      (∑ u∈paresCompatibles n,|c t u*(marcaDelPar (next X a) t u-marcaDelPar X t u)|)≤W*(10*n) := by
    apply (Finset.sum_le_sum (fun u hu => each t u hu)).trans
    rw [←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ wp
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)).trans
      (suma_cambios_del_patron hn X a good live t)
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun t _ => pat t)).trans_eq
  simp [CuatroMarcas]; ring

theorem cambio_de_pesos_en_soporte {n} (X : State n) (g : Legal X.physical) (W : ℝ) (wp : 0≤W)
    (c : CuatroMarcas→Mark n→ℝ) (cap : ∀ t,∀ u∈paresCompatibles n,|c t u|≤W*(escalaDelPatron n t:ℝ)) :
    ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,|c t u*marcaDelPar X t u|≤16*W*(n:ℝ)^2 := by
  have pat (t : CuatroMarcas) : (∑ u∈paresCompatibles n,|c t u*marcaDelPar X t u|)≤W*n^2 := by
    calc _ ≤ ∑ u∈paresCompatibles n,W*((escalaDelPatron n t:ℝ)*marcaDelPar X t u) := by
            apply Finset.sum_le_sum; intro u hu
            have nn : 0≤marcaDelPar X t u := escalar_no_negativo _
            simp only [abs_mul,abs_of_nonneg nn,←mul_assoc]
            exact mul_le_mul_of_nonneg_right (cap t u hu) (escalar_no_negativo _)
         _ ≤ _ := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (masa_del_patron_antes_del_paso X g t) wp
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun t _ => pat t)).trans_eq
  simp [CuatroMarcas]; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_del_patron_antes_del_paso
#print axioms ArticuloA.Historias.variacion_del_atomo_completo
#print axioms ArticuloA.Historias.cambio_de_pesos_en_soporte
