import TestigoTrigonometricoDeDEF
import CotaElementalDelCosenoEnElCuarto
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil Real
open scoped Interval
def proyeccionDelTestigo (a : Bool) (s : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..(1-|s|),testigoDEF34 (t+max s 0)
    (if a then 1-(t+max (-s) 0) else t+max (-s) 0)

theorem masa_del_segmento_del_testigo {s : ℝ} (sl : 0≤s) (sr : s≤1) :
    (∫ t in (0:ℝ)..(1-s),testigoDEF34 (t+s) t) ≤ 9/10 := by
  let f (t : ℝ):=testigoDEF34 (t+s) t
  have cf : Continuous f := continuous_const.sub ((continuous_const.mul
    (Real.continuous_cos.comp (continuous_const.mul (continuous_id.add continuous_const)))).mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
  have pos : 0≤1-s := sub_nonneg.mpr sr
  have le : 1-s≤1 := by linarith
  by_cases small : s≤1/4
  · have full:=promedio_completo_de_la_diagonal s
    change (∫ t in (0:ℝ)..1,f t)=_ at full
    have split:=intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ:=volume) 0 (1-s))
      (cf.intervalIntegrable (μ:=volume) (1-s) 1)
    have tail:=intervalIntegral.integral_mono_on (μ:=volume) le (intervalIntegrable_const (c:=(4/5:ℝ)))
      (cf.intervalIntegrable (μ:=volume) (1-s) 1) (fun t _=>(cotas_del_testigo_DEF (t+s) t).1)
    rw [intervalIntegral.integral_const,smul_eq_mul] at tail
    change (∫ t in (0:ℝ)..(1-s),f t)≤_
    linarith only [tail,split,full,perdida_menor_que_ocho_por_el_desplazamiento sl small]
  · have ub:=intervalIntegral.integral_mono_on (μ:=volume) pos (cf.intervalIntegrable (μ:=volume) 0 (1-s))
      (intervalIntegrable_const (c:=(6/5:ℝ))) (fun t _=>(cotas_del_testigo_DEF (t+s) t).2)
    rw [intervalIntegral.integral_const,smul_eq_mul] at ub
    change (∫ t in (0:ℝ)..(1-s),f t)≤_
    linarith only [le_of_not_ge small,ub]

theorem ambas_proyecciones_del_testigo (a : Bool) {s : ℝ} (hs : |s|≤1) :
    proyeccionDelTestigo a s ≤ 9/10 := by
  have eq : proyeccionDelTestigo a s=(∫ t in (0:ℝ)..(1-|s|),testigoDEF34 (t+|s|) t) := by
    unfold proyeccionDelTestigo
    apply intervalIntegral.integral_congr
    intro t _
    cases a <;> simp only [Bool.false_eq_true,if_false,if_true,(simetrias_del_testigo _ _).2]
    all_goals
      by_cases sign : 0≤s
      · simp [abs_of_nonneg sign,max_eq_left sign,max_eq_right (neg_nonpos.mpr sign)]
      · have neg : s≤0 := le_of_not_ge sign
        simpa [abs_of_nonpos neg,max_eq_right neg,max_eq_left (neg_nonneg.mpr neg)] using (simetrias_del_testigo t (t+-s)).1
  exact eq.le.trans (masa_del_segmento_del_testigo (abs_nonneg _) hs)

theorem diagonal_central_del_testigo (a : Bool) : proyeccionDelTestigo a 0=9/10 := by
  have eq:=promedio_completo_de_la_diagonal 0
  cases a
  · norm_num [proyeccionDelTestigo] at eq ⊢; exact eq
  · norm_num [proyeccionDelTestigo,fun t=>(simetrias_del_testigo t t).2] at eq ⊢; exact eq
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_del_segmento_del_testigo
#print axioms ArticuloA.Historias.ambas_proyecciones_del_testigo
#print axioms ArticuloA.Historias.diagonal_central_del_testigo
