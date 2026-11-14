import MonotoniaIntegralDelDualAnclado
import CamposNormalizadosParaLaTraslacion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
def energiaRealB34 (r d a : ℝ→ℝ) :=
  (energia unidad r).toReal+(energia diag d).toReal+(energia anti a).toReal

theorem energia_real_de_una_linea (l r : ℝ) {f : ℝ→ℝ} (fc : Continuous f) :
    (energia (volume.restrict (Icc l r)) f).toReal=∫ s,f s^2 ∂volume.restrict (Icc l r) :=
  (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _=>sq_nonneg _))
    (fc.pow 2).aestronglyMeasurable).symm

theorem coercividad_entre_densidades_positivas {U V : ℝ×ℝ→ℝ} {D D' A A' r d a : ℝ→ℝ}
    {c κ : ℝ} (cp : 0<c) (kp : 0<κ) (uc : Continuous U) (vc : Continuous V)
    (dc : Continuous D) (dc' : Continuous D') (ac : Continuous A) (ac' : Continuous A')
    (cr : Continuous r) (cd : Continuous d) (ca : Continuous a)
    (bandU : ∀ z,c≤U z ∧ c≤V z) (bandD : ∀ t,κ≤D t ∧ κ≤D' t) (bandA : ∀ t,κ≤A t ∧ κ≤A' t)
    (eqU : ∀ z,Real.log (U z)+sumaLevantada false r d a z=Real.log (V z))
    (eqD : ∀ t,Real.log (D t)+d t=Real.log (D' t)) (eqA : ∀ t,Real.log (A t)+a t=Real.log (A' t)) :
    min (c/2) (κ/5)*energiaRealB34 r d a≤
      (∫ z,(V z-U z)*sumaLevantada false r d a z ∂cuadrado)+
      (∫ t,(D' t-D t)*d t ∂diag)+(∫ t,(A' t-A t)*a t ∂anti) := by
  let S:=sumaLevantada false r d a
  have sc : Continuous S := ((cr.comp continuous_fst).add (cd.comp (continuous_fst.sub continuous_snd))).add
    (ca.comp (continuous_fst.add continuous_snd))
  have logsQ (z) : Real.exp (Real.log (U z)+S z)=V z :=
    (congrArg Real.exp (eqU z)).trans (Real.exp_log (cp.trans_le (bandU z).2))
  have logsD (t) : Real.exp (Real.log (D t)+d t)=D' t :=
    (congrArg Real.exp (eqD t)).trans (Real.exp_log (kp.trans_le (bandD t).2))
  have logsA (t) : Real.exp (Real.log (A t)+a t)=A' t :=
    (congrArg Real.exp (eqA t)).trans (Real.exp_log (kp.trans_le (bandA t).2))
  have pu z:=Real.exp_log (cp.trans_le (bandU z).1)
  have pd t:=Real.exp_log (kp.trans_le (bandD t).1)
  have pa t:=Real.exp_log (kp.trans_le (bandA t).1)
  have sqint : Integrable (fun z=>S z^2) cuadrado := by
    rw [cuadrado,unidad,Measure.prod_restrict]
    exact (sc.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have wi : Integrable (fun z=>(V z-U z)*S z) cuadrado := by
    rw [cuadrado,unidad,Measure.prod_restrict]
    exact ((vc.sub uc).mul sc).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have wc:=dual_anclado_por_diferencias false r d a cr.measurable cd.measurable ca.measurable
    (fun z=>Real.log (U z)) (fun t=>Real.log (D t)) (fun t=>Real.log (A t)) 1 c κ zero_le_one cp.le kp.le
    sqint (cd.pow 2).continuousOn.integrableOn_Icc (ca.pow 2).continuousOn.integrableOn_Icc
    (by simpa only [←show S=sumaLevantada false r d a from rfl,one_mul,logsQ,pu] using wi)
    (by simpa only [one_mul,logsD,pd] using (show Integrable (fun t=>(D' t-D t)*d t) diag from
      ((dc'.sub dc).mul cd).continuousOn.integrableOn_Icc))
    (by simpa only [one_mul,logsA,pa] using (show Integrable (fun t=>(A' t-A t)*a t) anti from
      ((ac'.sub ac).mul ca).continuousOn.integrableOn_Icc))
    (Filter.Eventually.of_forall (fun z=>by simpa only [←show S=sumaLevantada false r d a from rfl,one_mul,logsQ,pu] using bandU z))
    (Filter.Eventually.of_forall (fun t=>by simpa only [logsD,pd] using bandD t))
    (Filter.Eventually.of_forall (fun t=>by simpa only [logsA,pa] using bandA t))
  simpa only [energiaRealB34,trabajoExp,←show S=sumaLevantada false r d a from rfl,one_mul,logsQ,pu,logsD,pd,logsA,pa] using wc
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.energia_real_de_una_linea
#print axioms ArticuloA.Historias.coercividad_entre_densidades_positivas
