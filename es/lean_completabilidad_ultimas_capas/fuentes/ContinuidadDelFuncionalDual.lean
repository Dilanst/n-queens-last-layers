import ControlIntegralDeLaDistanciaDual
import IntegralesDeLaProyeccionUniforme
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped Topology
local instance : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance

private theorem integral_lipschitz {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g v : α→ℝ}
    (fi : Integrable f μ) (gi : Integrable g μ) (vi : Integrable v μ) (b : ∀ s,|f s-g s|≤v s) :
    |(∫ s,f s ∂μ)-∫ s,g s ∂μ|≤∫ s,v s ∂μ := by
  rw [←integral_sub fi gi]
  exact (norm_integral_le_integral_norm _).trans (integral_mono (fi.sub gi).norm vi b)

theorem costo_dual_continuo {H : ℝ} (hp : 0≤H) (i : Fin 4) : Continuous (fun u : CajaDual H=>costoDual u i) := by
  apply LipschitzWith.continuous (K:=4)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have diff s : |potencialDeHolgura (campoDual u i s)-potencialDeHolgura (campoDual v i s)|≤
      2*diferenciaDual u v i s := by
    let y:=campoDual u i s; let z:=campoDual v i s
    have e:=abs_exp_neg_lipschitz (campo_dual_acotado hp u i s).1 (campo_dual_acotado hp v i s).1
    have eq : potencialDeHolgura y-potencialDeHolgura z=(y-z)+(exp (-y)-exp (-z)) := by unfold potencialDeHolgura; ring
    change |potencialDeHolgura y-potencialDeHolgura z|≤2*|y-z|; rw [eq]
    exact (abs_add_le _ _).trans (by change |y-z|+|exp (-y)-exp (-z)|≤_; change |exp (-y)-exp (-z)|≤|y-z| at e; linarith)
  have b:=integral_lipschitz (costo_dual_integrable hp u i) (costo_dual_integrable hp v i)
    ((integrable_diferencia_dual hp u v i).const_mul 2) diff
  change |costoDual u i-costoDual v i|≤∫ s,2*diferenciaDual u v i s ∂marginalRef i at b
  rw [integral_const_mul] at b
  change |costoDual u i-costoDual v i|≤4*dist u v
  linarith [integral_diferencia_dual hp u v i]

theorem particion_dual_continua {H : ℝ} (hp : 0≤H) : Continuous (particionDual (H:=H)) := by
  apply LipschitzWith.continuous (K:=8)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  let g (i : Fin 4) (z : ℝ×ℝ):=diferenciaDual u v i (coord i z)
  have gi i : Integrable (g i) cuadrado := integral_acotada_dual
    ((diferencia_dual_medible u v i).comp (coord_medible i))
    (fun z=>(abs_abs _).le.trans (diferencia_dual_acotada hp u v i (coord i z)))
  have comp i : (∫ z,g i z ∂cuadrado)≤2*dist u v := by
    apply (integral_del_levantamiento_acotado i (diferencia_dual_medible u v i)
      (fun s=>(abs_abs _).le.trans (diferencia_dual_acotada hp u v i s)) (fun _=>abs_nonneg _)).trans
    exact integral_diferencia_dual hp u v i
  have diff z : |exp (-sumaDual u z)-exp (-sumaDual v z)|≤∑ i : Fin 4,g i z := by
    apply (abs_exp_neg_lipschitz (suma_dual_acotada hp u z).1 (suma_dual_acotada hp v z).1).trans
    unfold sumaDual; rw [←Finset.sum_sub_distrib]; exact Finset.abs_sum_le_sum_abs _ _
  have b:=integral_lipschitz (densidad_dual_integrable hp u) (densidad_dual_integrable hp v)
    (integrable_finset_sum _ (fun i _=>gi i)) diff
  change |particionDual u-particionDual v|≤∫ z,∑ i : Fin 4,g i z ∂cuadrado at b
  rw [integral_finset_sum _ (fun i _=>gi i)] at b
  apply b.trans
  exact (Finset.sum_le_sum (fun i _=>comp i)).trans_eq (by simp; ring)

theorem funcional_dual_continuo {H : ℝ} (hp : 0≤H) (d : ℝ) : Continuous (funcionalDual (H:=H) d) :=
  (continuous_finset_sum _ (fun i _=>costo_dual_continuo hp i)).add
    (continuous_const.mul ((particion_dual_continua hp).log (fun u=>((exp_pos _).trans_le (particion_dual_acotada hp u).1).ne')))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.costo_dual_continuo
#print axioms ArticuloA.Historias.particion_dual_continua
#print axioms ArticuloA.Historias.funcional_dual_continuo
