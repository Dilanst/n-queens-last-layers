import MediasGeometricasDeLosFactores
import MarginalesDesdeElTableroSinLipschitz
import IdentidadesDeLaDensidadSeparada
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def indiceTransversal (col : Bool) : Fin 4 := if col then 1 else 0

theorem euler_reciproco_de_la_fibra {P p x b} (e : EulerFisica P p x b)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (s : ℝ) (hs : s∈rangoF i) :
    1/camposFisicos p i s=coefLinea x i+b*cavidadFisica (camposFisicos p) i s := by
  have eq:=ecuacion_puntual_sin_lipschitz x cp i (ecuaciones_de_fibra_desde_euler_medida e cp i) s hs
  exact (div_eq_iff (pos i s hs).ne').mpr ((mul_comm _ _).trans eq).symm

theorem techo_de_las_oblicuas_fisicas {P p x b} (e : EulerFisica P p x b)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (di : ¬i.val<2) (s : ℝ) (hs : s∈rangoF i) : camposFisicos p i s≤1 := by
  have non : 0≤cavidadFisica (camposFisicos p) i s := by
    apply intervalIntegral.integral_nonneg (longitud_en_unidad i hs).1
    intro t _
    exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) (NNReal.coe_nonneg _)
  have eq:=euler_reciproco_de_la_fibra e cp pos i s hs
  simp only [coefLinea,if_neg di] at eq
  have H : 1≤1/camposFisicos p i s := by linarith only [eq,mul_nonneg e.coef.le non]
  simpa only [one_mul] using (le_div_iff₀ (pos i s hs)).mp H

theorem cavidad_transversal_como_media (p : FactoresContinuos) (x : ℝ≥0) (col : Bool)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
    cavidadFisica (camposFisicos p) (indiceTransversal col) s =
      ∫ t,campoR15 p (indiceTransversal (!col)) t*nucleoEnUnaTransversal p x col s t ∂unidad := by
  rw [integral_en_el_intervalo_unitario]
  have len : longitudDeCuerda (indiceTransversal col) s=1 := by cases col <;> rfl
  unfold cavidadFisica; rw [len]
  apply intervalIntegral.integral_congr
  intro t ht; rw [uIcc_of_le zero_le_one] at ht
  have eq (j : Fin 3) : restriccionACuerda (camposFisicos p) (indiceTransversal col) s t j=
      campoR15 p (familiaTransversal (indiceTransversal col) j)
        (coord (familiaTransversal (indiceTransversal col) j) (puntoDeCuerda (indiceTransversal col) s t)) := by
    rw [coordenada_transversal_afin]
    apply (campo_dentro_de_su_intervalo p _ _).symm
    apply etiqueta_en_el_intervalo_fisico
    · cases col <;> exact hs
    · rwa [len]
  simp only [productoEnCuerda,eq]
  cases col <;> simp [nucleoEnUnaTransversal,indiceTransversal,holguraInteriorR5,coefLinea,
    familiaTransversal,puntoDeCuerda,coord,show ¬(3:Fin 4).val<2 by decide,mul_assoc,add_comm]

theorem limites_de_la_cavidad_transversal {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (col : Bool) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
    mediaGeometrica (campoR15 p (indiceTransversal (!col)))*exp (-costoTotalR7 p x)≤
      cavidadFisica (camposFisicos p) (indiceTransversal col) s ∧
    cavidadFisica (camposFisicos p) (indiceTransversal col) s≤1 := by
  let j:=indiceTransversal (!col)
  let r:=campoR15 p j
  have rc:=campo_continuo_por_recorte cp j
  have rp t : 0<r t := pos j _ (recorte_dentro j t)
  rw [cavidad_transversal_como_media p x col s hs]
  refine ⟨promedio_ponderado_de_la_fibra e xp cp pos s hs col rc rp,?_⟩
  have top (i : Fin 4) (hi : ¬i.val<2) t : holguraInteriorR5 p x i t≤1 := by
    simp only [holguraInteriorR5,coefLinea,if_neg hi,one_mul]
    exact techo_de_las_oblicuas_fisicas e cp pos i hi _ (recorte_dentro i t)
  have dc : Continuous (fun t=>holguraInteriorR5 p x 2 (if col then t-s else s-t)) := by
    have hc:=(vacancia_fisica_y_logaritmo e xp cp pos 2).1
    cases col
    · exact hc.comp (continuous_const.sub continuous_id)
    · exact hc.comp (continuous_id.sub continuous_const)
  have ac : Continuous (fun t=>holguraInteriorR5 p x 3 (s+t)) := (vacancia_fisica_y_logaritmo e xp cp pos 3).1.comp (continuous_const.add continuous_id)
  have ri : Integrable r unidad:=rc.continuousOn.integrableOn_Icc
  have fi : Integrable (fun t=>r t*nucleoEnUnaTransversal p x col s t) unidad :=
    (rc.mul (dc.mul ac)).continuousOn.integrableOn_Icc
  have norm:=normalizacion_R15_en_masa_interior e xp j (by cases col <;> decide)
  apply (integral_mono fi ri (fun t=>?_)).trans norm.le
  have d1:=top 2 (by decide) (if col then t-s else s-t)
  have a1:=top 3 (by decide) (s+t)
  have ap:=(vacancia_fisica_y_logaritmo e xp cp pos 3).2.1 (s+t)
  have k1 : nucleoEnUnaTransversal p x col s t≤1 := (mul_le_mul_of_nonneg_right d1 ap.le).trans (by simpa only [one_mul] using a1)
  exact (mul_le_mul_of_nonneg_left k1 (rp t).le).trans_eq (mul_one _)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_reciproco_de_la_fibra
#print axioms ArticuloA.Historias.techo_de_las_oblicuas_fisicas
#print axioms ArticuloA.Historias.cavidad_transversal_como_media
#print axioms ArticuloA.Historias.limites_de_la_cavidad_transversal
