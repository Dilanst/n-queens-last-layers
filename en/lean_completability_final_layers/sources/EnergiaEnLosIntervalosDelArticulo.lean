import SaltosDeLosCamposEnLaDensidad
import CoercividadParaDosDensidadesPositivas
import TraslacionConLaEnergiaDeLasCuatroFamilias
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def cuatroLogTrasladados (R C D A : ℝ→ℝ) (t : ℝ) : Fin 4→ℝ→ℝ
  | 0,s=>Real.log (R (s+t))
  | 1,s=>Real.log (C s)
  | 2,s=>Real.log (D (s+t))
  | 3,s=>Real.log (A (s+t))

theorem energia_al_integrar_el_salto {f : ℝ→ℝ} (cf : Continuous f) {l r : ℝ} (lr : l≤r) :
    (∫ s in l..r,f s^2)=(energia (volume.restrict (Icc l r)) f).toReal := by
  rw [energia_real_de_una_linea l r cf,intervalIntegral.integral_of_le lr,integral_Icc_eq_integral_Ioc]

theorem energia_del_articulo_para_la_columna_fija (R C D A : ℝ→ℝ) (t : ℝ)
    (cr : Continuous (saltoLogB33 R t)) (cd : Continuous (saltoLogB33 D t)) (ca : Continuous (saltoLogB33 A t)) :
    (∑ g,energiaDeDiferencias (cuatroLogTrasladados R C D A t) (cuatroLogTrasladados R C D A 0) g)=
      energiaRealB34 (saltoLogB33 R t) (saltoLogB33 D t) (saltoLogB33 A t) := by
  rw [Fin.sum_univ_four]
  have eC : energiaDeDiferencias (cuatroLogTrasladados R C D A t) (cuatroLogTrasladados R C D A 0) 1=0 := by
    simp [energiaDeDiferencias,masaExterior,cuatroLogTrasladados]
  rw [eC,add_zero]
  simp only [energiaDeDiferencias,masaExterior,cuatroLogTrasladados,add_zero,extremoIzq,extremoDer]
  change (∫ s in (0:ℝ)..1,saltoLogB33 R t s^2)+(∫ s in (-1:ℝ)..1,saltoLogB33 D t s^2)+
    (∫ s in (0:ℝ)..2,saltoLogB33 A t s^2)=_
  rw [energia_al_integrar_el_salto cr (by norm_num : (0:ℝ)≤1),
    energia_al_integrar_el_salto cd (by norm_num : (-1:ℝ)≤1),energia_al_integrar_el_salto ca (by norm_num : (0:ℝ)≤2)]
  rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.energia_al_integrar_el_salto
#print axioms ArticuloA.Historias.energia_del_articulo_para_la_columna_fija
