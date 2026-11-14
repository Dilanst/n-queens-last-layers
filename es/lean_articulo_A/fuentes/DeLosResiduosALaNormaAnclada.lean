import CoercividadParaDosDensidadesPositivas
import TrabajoDelGradienteEnDosDiagonales
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Interval
/-- Both squares may include extensions of the original physical profile. The
    column is fixed. There are only two error terms left after the row pairing. -/
theorem ganancia_anclada_por_dos_residuos {U : ℝ×ℝ→ℝ} {r d a D A : ℝ→ℝ} {Z coef : ℝ}
    (uc : Continuous U) (cr : Continuous r) (cd : Continuous d) (ca : Continuous a)
    (cD : Continuous D) (cA : Continuous A) (lp : 0<coef) (zp : 0≤Z)
    (coerc : coef*energiaRealB34 r d a≤(∫ z,U z*sumaLevantada false r d a z ∂cuadrado)+
      (∫ s,D s*d s ∂diag)+(∫ s,A s*a s ∂anti))
    (row : ∀ s∈Icc (0:ℝ) 1,(∫ c in (0:ℝ)..1,U (s,c))*r s≤0)
    (diagB : ∀ s∈Icc (-1:ℝ) 1,|cargaDeFranja U 1 s+D s|≤Z)
    (antiB : ∀ s∈Icc (0:ℝ) 2,|cargaDeFranja U 2 s+A s|≤Z) :
    coef*Real.sqrt (energiaRealB34 r d a)≤2*Z := by
  rw [trabajo_por_las_tres_proyecciones uc cr cd ca] at coerc
  have neg : (∫ s,(∫ c in (0:ℝ)..1,U (s,c))*r s ∂unidad)≤0 :=
    integral_nonpos_of_ae ((ae_restrict_mem (μ:=volume) measurableSet_Icc).mono (fun s hs=>row s hs))
  have bd:=pareja_diagonal_con_residual 1 uc cd cD (coef:=coef) (by norm_num : (1:ℝ)-(-1)=2) diagB
  have ba:=pareja_diagonal_con_residual 2 uc ca cA (coef:=coef) (by norm_num : (2:ℝ)-0=2) antiB
  change 2*coef*((∫ s,cargaDeFranja U 1 s*d s ∂diag)+(∫ s,D s*d s ∂diag))≤
    2*Z^2+coef^2*(∫ s,d s^2 ∂diag) at bd
  change 2*coef*((∫ s,cargaDeFranja U 2 s*a s ∂anti)+(∫ s,A s*a s ∂anti))≤
    2*Z^2+coef^2*(∫ s,a s^2 ∂anti) at ba
  have ed : (∫ t,d t^2 ∂diag)=(energia diag d).toReal := (energia_real_de_una_linea (-1) 1 cd).symm
  have ea : (∫ t,a t^2 ∂anti)=(energia anti a).toReal := (energia_real_de_una_linea 0 2 ca).symm
  rw [ed] at bd
  rw [ea] at ba
  have paired : coef*energiaRealB34 r d a≤
    ((∫ s,cargaDeFranja U 1 s*d s ∂diag)+(∫ s,D s*d s ∂diag))+
    ((∫ s,cargaDeFranja U 2 s*a s ∂anti)+(∫ s,A s*a s ∂anti)) := by linarith only [coerc,neg]
  have scale:=mul_le_mul_of_nonneg_left paired (show 0≤2*coef by positivity)
  have rowEnergy : 0≤coef^2*(energia unidad r).toReal := mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have en : 0≤energiaRealB34 r d a := by unfold energiaRealB34; positivity
  have square : coef^2*energiaRealB34 r d a≤4*Z^2 := by
    change 2*coef*(_+_)≤2*Z^2+coef^2*(energia diag d).toReal at bd
    change 2*coef*(_+_)≤2*Z^2+coef^2*(energia anti a).toReal at ba
    dsimp only [energiaRealB34] at scale ⊢
    linarith only [bd,ba,scale,rowEnergy]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow,Real.sq_sqrt en]
  nlinarith only [square]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ganancia_anclada_por_dos_residuos
