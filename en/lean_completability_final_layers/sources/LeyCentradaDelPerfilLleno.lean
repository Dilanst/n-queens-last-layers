import EntropiaEnElCuadradoCentrado
open Set MeasureTheory Filter
open scoped NNReal ENNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

def centrar (z : ℝ×ℝ) : ℝ×ℝ := (z.1-1/2,z.2-1/2)
def traslado : Fin 4→ℝ | 0 => 1/2 | 1 => 1/2 | 2 => 0 | 3 => 1
def refCentrada (i : Fin 4) : Measure ℝ := if i.val<2 then volume.restrict (Ioc (-(1/2:ℝ)) (1/2))
  else volume.restrict (Ioc (-1:ℝ) 1)
def leyCentrada (P : TableroMedido) := (cuadrado.withDensity (fun z => P.ν z)).map centrar

theorem mover_referencia (a b d : ℝ) : (volume.restrict (Ioc a b)).map (·-d)=
    volume.restrict (Ioc (a-d) (b-d)) := by
  have e : (fun x : ℝ => x+(-d)) ⁻¹' Ioc (a-d) (b-d)=Ioc a b := by
    ext x; simp only [mem_preimage,mem_Ioc]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simp only [sub_eq_add_neg] at e ⊢
  rw [←e,←Measure.restrict_map (show Measurable (fun x : ℝ => x + -d) from measurable_id.add_const _) measurableSet_Ioc,map_add_right_eq_self]

theorem referencia_de_cada_coordenada (i : Fin 4) :
    (marginalRef i).map (·-traslado i)=refCentrada i := by
  fin_cases i <;> simp only [marginalRef,traslado,refCentrada,mover_referencia] <;> norm_num

theorem marginal_centrada (P : TableroMedido) (i : Fin 4) :
    (leyCentrada P).map (coord i)=((marginalRef i).withDensity (fun t => P.m i t)).map (·-traslado i) := by
  have mc : Measurable centrar := (measurable_fst.sub_const _).prodMk (measurable_snd.sub_const _)
  rw [leyCentrada,←P.ley.imagen,Measure.map_map (coord_medible i) mc,
    Measure.map_map (show Measurable (fun x : ℝ => x-traslado i) from measurable_id.sub_const _) (coord_medible i)]
  congr 1; funext z; fin_cases i <;> simp [Function.comp,coord,centrar,traslado]; ring

theorem filas_y_columnas_uniformes {P p b} (h : EulerFisica P p 0 b) (i : Fin 4) (rc : i.val<2) :
    (leyCentrada P).map (coord i)=refCentrada i := by
  have eq : (fun t => (↑(P.m i t):ℝ≥0∞)) =ᵐ[marginalRef i] 1 := by
    filter_upwards [vacancia_transversal_llena h i rc] with t ht
    change 1-(P.m i t:ℝ)=0 at ht
    have z : (P.m i t:ℝ)=1 := by linarith
    have r : P.m i t=1 := by exact_mod_cast z
    simp [r]
  rw [marginal_centrada,withDensity_congr_ae eq,withDensity_one,referencia_de_cada_coordenada]

theorem dominacion_de_las_oblicuas (P : TableroMedido) (i : Fin 4) :
    (leyCentrada P).map (coord i)≤refCentrada i := by
  have leq : (fun t => (↑(P.m i t):ℝ≥0∞)) ≤ᵐ[marginalRef i] 1 := by
    filter_upwards [P.admisible i] with t ht
    change (↑(P.m i t):ℝ≥0∞)≤1; exact_mod_cast ht
  rw [marginal_centrada,←referencia_de_cada_coordenada]
  apply Measure.map_mono _ (measurable_id.sub_const _)
  simpa only [withDensity_one] using withDensity_mono leq

theorem masa_centrada_uno {P p b} (h : EulerFisica P p 0 b) : leyCentrada P univ=1 := by
  have e:=congrArg (fun μ : Measure ℝ => μ univ) (filas_y_columnas_uniformes h 0 (by decide))
  change ((leyCentrada P).map (coord 0)) univ = refCentrada 0 univ at e
  rw [Measure.map_apply (coord_medible 0) MeasurableSet.univ,preimage_univ] at e
  convert e using 1
  norm_num [refCentrada,Measure.restrict_apply,Real.volume_Ioc]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.filas_y_columnas_uniformes
#print axioms ArticuloA.Historias.dominacion_de_las_oblicuas
#print axioms ArticuloA.Historias.masa_centrada_uno
