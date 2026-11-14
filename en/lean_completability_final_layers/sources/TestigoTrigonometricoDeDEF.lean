import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RepresentanteFisicoDeLosCuatroLimites
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil Real
open scoped Interval
def testigoDEF34 (r c : ℝ) := 1-(1/5:ℝ)*cos (2*π*r)*cos (2*π*c)

theorem cotas_del_testigo_DEF (r c : ℝ) : 4/5≤testigoDEF34 r c ∧ testigoDEF34 r c≤6/5 := by
  have v : |cos (2*π*r)*cos (2*π*c)|≤1 := by
    rw [abs_mul]; exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have pair:=abs_le.mp v
  unfold testigoDEF34; constructor <;> linarith [pair.1,pair.2]

theorem simetrias_del_testigo (r c : ℝ) :
    testigoDEF34 r c=testigoDEF34 c r ∧ testigoDEF34 r (1-c)=testigoDEF34 r c := by
  unfold testigoDEF34
  constructor
  · ring
  · rw [show 2*π*(1-c)=2*π-(2*π*c) by ring,Real.cos_two_pi_sub]

theorem integral_por_dos_mitades_opuestas {f : ℝ→ℝ} (cf : Continuous f) (h u : ℝ)
    (flip : ∀ t,f (t+u) = -f t) : (∫ t in h..(h+2*u),f t)=0 := by
  have trans:=intervalIntegral.integral_comp_add_right (a:=h) (b:=h+u) f u
  simp_rw [flip] at trans
  rw [intervalIntegral.integral_neg,show h+u+u=h+2*u by ring] at trans
  have split:=intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ:=volume) h (h+u))
    (cf.intervalIntegrable (μ:=volume) (h+u) (h+2*u))
  linarith only [trans,split]

theorem coseno_de_un_periodo (d : ℝ) : (∫ t in (0:ℝ)..1,cos (2*π*t+d))=0 := by
  have c : Continuous (fun t : ℝ=>cos (2*π*t+d)) := Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  have z:=integral_por_dos_mitades_opuestas c 0 (1/2) (fun t=>by
    rw [show 2*π*(t+1/2)+d=2*π*t+d+π by ring,Real.cos_add_pi])
  norm_num at z; exact z

theorem coseno_de_dos_periodos (d : ℝ) : (∫ t in (0:ℝ)..1,cos (4*π*t+d))=0 := by
  let f:=fun t : ℝ=>cos (4*π*t+d)
  have c : Continuous f := Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  have z (h : ℝ):=integral_por_dos_mitades_opuestas c h (1/4) (fun t=>by
    change cos (4*π*(t+1/4)+d)= -cos (4*π*t+d)
    rw [show 4*π*(t+1/4)+d=4*π*t+d+π by ring,Real.cos_add_pi])
  have l:=z 0; have r:=z (1/2); norm_num at l r
  have both:=intervalIntegral.integral_add_adjacent_intervals (c.intervalIntegrable (μ:=volume) 0 (1/2))
    (c.intervalIntegrable (μ:=volume) (1/2) 1)
  change (∫ t in (0:ℝ)..1,f t)=0
  linarith only [l,r,both]

theorem transversales_unitarias_del_testigo (s : ℝ) :
    (∫ c in (0:ℝ)..1,testigoDEF34 s c)=1 ∧ (∫ r in (0:ℝ)..1,testigoDEF34 r s)=1 := by
  have zero : (∫ c in (0:ℝ)..1,cos (2*π*c))=0 := by
    simpa using coseno_de_un_periodo 0
  have row : (∫ c in (0:ℝ)..1,testigoDEF34 s c)=1 := by
    have cf : Continuous (fun c : ℝ=>(1/5:ℝ)*cos (2*π*s)*cos (2*π*c)) :=
      continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    unfold testigoDEF34; rw [intervalIntegral.integral_sub (intervalIntegrable_const (c:=(1:ℝ)))
      (cf.intervalIntegrable (μ:=volume) 0 1),
      intervalIntegral.integral_const_mul,zero]; simp
  refine ⟨row,?_⟩
  exact (intervalIntegral.integral_congr (fun r _=>(simetrias_del_testigo r s).1)).trans row

theorem promedio_completo_de_la_diagonal (s : ℝ) :
    (∫ t in (0:ℝ)..1,testigoDEF34 (t+s) t)=1-cos (2*π*s)/10 := by
  let d:=2*π*s
  have cc : Continuous (fun t : ℝ=>cos (4*π*t+d)) := Real.continuous_cos.comp ((continuous_const.mul continuous_id).add continuous_const)
  have expr (t : ℝ) : testigoDEF34 (t+s) t=(1-cos d/10)-(1/10:ℝ)*cos (4*π*t+d) := by
    have h:=Real.two_mul_cos_mul_cos (2*π*(t+s)) (2*π*t)
    rw [show 2*π*(t+s)-2*π*t=d by dsimp [d]; ring,show 2*π*(t+s)+2*π*t=4*π*t+d by dsimp [d]; ring] at h
    unfold testigoDEF34; linarith only [h]
  simp_rw [expr]
  rw [intervalIntegral.integral_sub intervalIntegrable_const ((continuous_const.mul cc).intervalIntegrable ..),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,coseno_de_dos_periodos]
  simp [d]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cotas_del_testigo_DEF
#print axioms ArticuloA.Historias.simetrias_del_testigo
#print axioms ArticuloA.Historias.integral_por_dos_mitades_opuestas
#print axioms ArticuloA.Historias.coseno_de_un_periodo
#print axioms ArticuloA.Historias.coseno_de_dos_periodos
#print axioms ArticuloA.Historias.transversales_unitarias_del_testigo
#print axioms ArticuloA.Historias.promedio_completo_de_la_diagonal
