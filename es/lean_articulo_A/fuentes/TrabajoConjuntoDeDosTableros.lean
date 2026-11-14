import ContraccionDeLasMarginalesFisicas
import CamposMediblesDeLaRama
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Set MeasureTheory Perfil
def trabajoRelativo (P Q : TableroMedido) :=
  ∫ z,((P.ν z:ℝ)-Q.ν z)*(Real.log (P.ν z)-Real.log (Q.ν z)) ∂cuadrado

theorem descomposicion_del_trabajo (P Q : TableroMedido) (l : ℝ) (v : Fin 4→ℝ→ℝ)
    (mv : ∀ i,Measurable (v i)) (bd : ∀ i,∃ C : ℝ,∀ s,‖v i s‖≤C)
    (eq : ∀ᵐ z ∂cuadrado,Real.log (P.ν z)-Real.log (Q.ν z)=l+∑ i,v i (coord i z)) :
    trabajoRelativo P Q=(P.rho-Q.rho)*l+
      ∑ i,∫ s,((P.m i s:ℝ)-Q.m i s)*v i s ∂marginalRef i := by
  let d:=fun z=>((P.ν z:ℝ)-Q.ν z)
  have iden : Integrable d cuadrado := P.masaFinita.sub Q.masaFinita
  have it (i : Fin 4) : Integrable (fun z=>d z*v i (coord i z)) cuadrado := by
    simpa only [mul_comm] using iden.bdd_mul ((mv i).comp (coord_medible i)).aestronglyMeasurable
      ⟨(bd i).choose,fun z=>(bd i).choose_spec (coord i z)⟩
  calc
    _ = ∫ z,d z*(l+∑ i,v i (coord i z)) ∂cuadrado := integral_congr_ae (eq.mono (fun _ H=>by rw [H]))
    _ = (∫ z,d z ∂cuadrado)*l+∑ i,∫ z,d z*v i (coord i z) ∂cuadrado := by
      simp_rw [mul_add,Finset.mul_sum]
      rw [integral_add (iden.mul_const l) (integrable_finset_sum _ (fun i _=>it i)),integral_mul_const,
        integral_finset_sum _ (fun i _=>it i)]
    _ = _ := by
      have mass : (∫ z,d z ∂cuadrado)=P.rho-Q.rho := integral_sub P.masaFinita Q.masaFinita
      rw [mass]
      congr 1
      exact Finset.sum_congr rfl fun i _=>(dualidad_de_la_diferencia P Q i (v i) (mv i) (bd i)).symm

theorem termino_de_linea_entre_densidades {a c f g M D : ℝ}
    (an : 0≤a) (fp : 0<f) (gp : 0<g) (gm : g≤M) (range : |Real.log f-Real.log g|≤D) :
    ((1-a*f)-(1-c*g))*(Real.log f-Real.log g) ≤ |c-a| *M*D := by
  have mon : 0≤(f-g)*(Real.log f-Real.log g) := by
    rcases le_total f g with h|h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr (Real.log_le_log fp h))
    · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (Real.log_le_log gp h))
  have dec : ((1-a*f)-(1-c*g))*(Real.log f-Real.log g) =
      (c-a)*g*(Real.log f-Real.log g)-a*((f-g)*(Real.log f-Real.log g)) := by ring
  rw [dec]
  apply (sub_le_self _ (mul_nonneg an mon)).trans ((le_abs_self _).trans _)
  rw [abs_mul,abs_mul,abs_of_pos gp]
  exact mul_le_mul (mul_le_mul_of_nonneg_left gm (abs_nonneg _)) range (abs_nonneg _)
    (mul_nonneg (abs_nonneg _) (gp.le.trans gm))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.descomposicion_del_trabajo
#print axioms ArticuloA.Historias.termino_de_linea_entre_densidades
