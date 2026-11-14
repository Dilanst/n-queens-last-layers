import EntradaDeConteoParaElPerfilCentrado
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped ENNReal

/-- Changing the origin of the board preserves Lebesgue measure on the plane. -/
theorem centrar_conserva_Lebesgue : (volume : Measure (ℝ×ℝ)).map centrar=volume := by
  let g (s : ℝ):=s+(-(1/2:ℝ))
  have gm : Measurable g:=measurable_id.add_const _
  have tr : (volume : Measure ℝ).map g=volume:=map_add_right_eq_self _ _
  have eq : centrar=Prod.map g g := by funext z; ext <;> simp [centrar,g,sub_eq_add_neg]
  rw [eq,Measure.volume_eq_prod,←Measure.map_prod_map _ _ gm gm,tr]

theorem ley_del_perfil_absolutamente_continua (P : TableroMedido) :
    leyCentrada P ≪ (volume : Measure (ℝ×ℝ)) := by
  have le : cuadrado≤(volume : Measure (ℝ×ℝ)) := by
    unfold cuadrado unidad; rw [Measure.prod_restrict,Measure.volume_eq_prod]; exact Measure.restrict_le_self
  have ac := (withDensity_absolutelyContinuous cuadrado (fun z=>(P.ν z:ℝ≥0∞))).trans le.absolutelyContinuous
  have mc : Measurable centrar := (measurable_fst.sub_const _).prodMk (measurable_snd.sub_const _)
  rw [←centrar_conserva_Lebesgue]; exact ac.map mc

/-- The centered probability of mass one satisfies the projection and AC conditions simultaneously. -/
theorem ley_llena_admisible_y_absolutamente_continua {P p b} (full : EulerFisica P p 0 b) :
    AdmisibleCentrada (leyCentrada P) ∧ leyCentrada P ≪ (volume : Measure (ℝ×ℝ)) :=
  ⟨admisibilidad_del_lleno full,ley_del_perfil_absolutamente_continua P⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.centrar_conserva_Lebesgue
#print axioms ArticuloA.Historias.ley_del_perfil_absolutamente_continua
#print axioms ArticuloA.Historias.ley_llena_admisible_y_absolutamente_continua
