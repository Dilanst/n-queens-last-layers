import TraslacionIntegralDeUnFactorMedible
import OscilacionIntegralDeTresFunciones
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

open scoped Topology
set_option maxHeartbeats 1000000 in
theorem oscilacion_de_cavidad_medible (f : Fin 4→ℝ→ℝ) (fi : ∀ i,Integrable (f i))
    (fm : ∀ i,Measurable (f i)) (M : ℝ) (cap : ∀ i y,|f i y|≤M) (i : Fin 4) {s v : ℝ} (hs : s∈rangoF i) :
    |cavidadFisica f i s-cavidadFisica f i v|≤
      M^2*(∑ j : Fin 3,(abs (pendienteTransversal i j)⁻¹) * 
        dist (traslacionEnL1 (fi (familiaTransversal i j)) (coord (familiaTransversal i j) (puntoDeCuerda i s 0)))
             (traslacionEnL1 (fi (familiaTransversal i j)) (coord (familiaTransversal i j) (puntoDeCuerda i v 0))))+
      M^3*|longitudDeCuerda i s-longitudDeCuerda i v| := by
  let A w t j:=restriccionACuerda f i w t j
  let l:=longitudDeCuerda i
  have M0 : 0≤M := (abs_nonneg _).trans (cap 0 0)
  have ab w t j : ‖A w t j‖≤M := cap _ _
  have am w j : Measurable (fun t=>A w t j) := (fm _).comp (etiqueta_continua i j w).measurable
  have whole:=oscilacion_de_integrales_de_tres (A s) (A v) (v:=l v) (longitud_en_unidad i hs).1 M0
    (ab s) (ab v) (am s) (am v)
  apply whole.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg M)
  apply Finset.sum_le_sum
  intro j _
  have ne : pendienteTransversal i j≠0 := by
    intro hz
    have h:=pendiente_absoluta_al_menos_uno i j
    norm_num [hz] at h
  exact distancia_integral_sobre_rectas (fi _) ne _ _ _

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscilacion_de_cavidad_medible
