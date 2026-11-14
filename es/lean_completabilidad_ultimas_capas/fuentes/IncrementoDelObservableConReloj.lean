import DieciseisPatronesEnUnMismoAtomo
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem cota_de_suma_doble {n} (g : CuatroMarcas→Mark n→ℝ) :
    |∑ t : CuatroMarcas,∑ u∈paresCompatibles n,g t u|≤∑ t : CuatroMarcas,∑ u∈paresCompatibles n,|g t u| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun t _ => Finset.abs_sum_le_sum_abs _ _)

theorem salto_con_reloj {n} (hn : 0<n) (X : State n) (a : Choice n) (good : coherent X)
    (ok : allowed X a) (c c' : CuatroMarcas→Mark n→ℝ) {W D : ℝ} (wp : 0≤W) (dp : 0≤D)
    (cap : ∀ t,∀ u∈paresCompatibles n,|c' t u|≤W*(escalaDelPatron n t:ℝ))
    (dif : ∀ t,∀ u∈paresCompatibles n,|c' t u-c t u|≤D*(escalaDelPatron n t:ℝ)) :
    |totalPonderado (next X a) c'-totalPonderado X c|≤160*W*n+16*D*(n:ℝ)^2 := by
  let m:=fun t u => marcaDelPar X t u
  let m':=fun t u => marcaDelPar (next X a) t u
  let dc:=fun t u => c' t u-c t u
  have eq : totalPonderado (next X a) c'-totalPonderado X c=
      (∑ t,∑ u∈paresCompatibles n,c' t u*(m' t u-m t u))+(∑ t,∑ u∈paresCompatibles n,dc t u*m t u) := by
    simp only [totalPonderado,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro u _; dsimp [m,m',dc]; ring
  rw [eq]
  exact (abs_add_le _ _).trans (add_le_add
    ((cota_de_suma_doble _).trans (variacion_del_atomo_completo hn X a good ok W wp c' cap))
    ((cota_de_suma_doble _).trans (cambio_de_pesos_en_soporte X good.1 D dp dc dif)))

/-- The difference from the frozen generator and the first linear clock term. -/
theorem resto_por_tiempo_y_estado {n} (hn : 0<n) (X : State n) (a : Choice n) (good : coherent X)
    (ok : allowed X a) (c c' v : CuatroMarcas→Mark n→ℝ) {D R : ℝ} (dp : 0≤D) (rp : 0≤R)
    (dif : ∀ t,∀ u∈paresCompatibles n,|c' t u-c t u|≤D*(escalaDelPatron n t:ℝ))
    (rem : ∀ t,∀ u∈paresCompatibles n,|c' t u-c t u-v t u|≤R*(escalaDelPatron n t:ℝ)) :
    let m:=marcaDelPar X
    let dm:=fun t u => marcaDelPar (next X a) t u-m t u
    |totalPonderado (next X a) c'-totalPonderado X c-
      ∑ t : CuatroMarcas,∑ u∈paresCompatibles n,(c t u*dm t u+v t u*m t u)|≤160*D*n+16*R*(n:ℝ)^2 := by
  intro m dm
  let dc:=fun t u => c' t u-c t u
  let r:=fun t u => dc t u-v t u
  have eq : totalPonderado (next X a) c'-totalPonderado X c-
      (∑ t,∑ u∈paresCompatibles n,(c t u*dm t u+v t u*m t u))=
      (∑ t,∑ u∈paresCompatibles n,dc t u*dm t u)+(∑ t,∑ u∈paresCompatibles n,r t u*m t u) := by
    simp only [totalPonderado,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro u _; dsimp [dc,r,dm,m]; ring
  rw [eq]
  exact (abs_add_le _ _).trans (add_le_add
    ((cota_de_suma_doble _).trans (variacion_del_atomo_completo hn X a good ok D dp dc dif))
    ((cota_de_suma_doble _).trans (cambio_de_pesos_en_soporte X good.1 R rp r rem)))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_de_suma_doble
#print axioms ArticuloA.Historias.salto_con_reloj
#print axioms ArticuloA.Historias.resto_por_tiempo_y_estado
