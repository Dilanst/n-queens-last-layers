import BandasDelNormalizadorYLasTransversales
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem banda_puntual_de_las_transversales {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (d : 0<1-(x:ℝ))
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (i : Fin 4) (rc : i.val<2) (s : ℝ) (hs : s∈rangoF i) :
    1/techoDEF35^2≤camposFisicos p i s ∧ camposFisicos p i s≤techoDEF35 := by
  have x1 : (x:ℝ)≤1 := by linarith only [d]
  obtain ⟨_,hi,_,_,br,bc⟩:=bandas_fisicas_de_las_medias e xp d cp pos
  have h (col : Bool) (dom : s∈Icc (0:ℝ) 1) :
      1/techoDEF35^2≤camposFisicos p (indiceTransversal col) s ∧ camposFisicos p (indiceTransversal col) s≤techoDEF35 := by
    have ds : s∈rangoF (indiceTransversal col) := by cases col <;> exact dom
    obtain ⟨lo,up⟩:=cotas_de_euler_por_transversal e xp x1 cp pos col s dom
    rw [campo_dentro_de_su_intervalo p _ ds] at lo up
    have bot : 1-(x:ℝ)≤b*mediaGeometrica (campoR15 p (indiceTransversal (!col))) := by
      cases col
      · exact bc
      · exact br
    exact banda_transversal_desde_el_reciproco x.coe_nonneg rfl techoDEF35_al_menos_uno
      (pos _ s ds) hi bot lo up
  rcases (show i=0 ∨ i=1 by omega) with rfl|rfl
  · exact h false hs
  · exact h true hs

theorem techo_de_la_cavidad_oblicua {p : FactoresContinuos} (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i))
    {M : ℝ} (mp : 0≤M)
    (rc : ∀ i : Fin 4,i.val<2 → ∀ t∈rangoF i,camposFisicos p i t≤M)
    (ob : ∀ i : Fin 4,¬i.val<2 → ∀ t∈rangoF i,camposFisicos p i t≤1)
    (i : Fin 4) (di : ¬i.val<2) (s : ℝ) (hs : s∈rangoF i) :
    cavidadFisica (camposFisicos p) i s≤M^2 := by
  have len:=longitud_en_unidad i hs
  have incl (j : Fin 3) {t : ℝ} (ht : t∈Icc 0 (longitudDeCuerda i s)) :=
    etiqueta_en_el_intervalo_fisico i j hs ht
  have h0 : (familiaTransversal i 0).val<2 ∧ (familiaTransversal i 1).val<2 ∧ ¬(familiaTransversal i 2).val<2 := by
    rcases (show i=2 ∨ i=3 by omega) with rfl|rfl <;> decide
  have bd {t} (ht : t∈Icc 0 (longitudDeCuerda i s)) : productoEnCuerda (camposFisicos p) i s t≤M^2 := by
    have a:=rc _ h0.1 _ (incl 0 ht)
    have c:=rc _ h0.2.1 _ (incl 1 ht)
    have v:=ob _ h0.2.2 _ (incl 2 ht)
    have ac:=mul_le_mul a c (NNReal.coe_nonneg _) mp
    have z:=mul_le_mul ac v (NNReal.coe_nonneg _) (mul_nonneg mp mp)
    simpa only [mul_one,pow_two,productoEnCuerda,restriccionACuerda,etiquetaEnCuerda] using z
  have ci:=producto_continuo_sobre_la_cuerda cp i hs
  have intg : IntervalIntegrable (productoEnCuerda (camposFisicos p) i s) volume 0 (longitudDeCuerda i s) := (by simpa only [uIcc_of_le len.1] using ci : ContinuousOn (productoEnCuerda (camposFisicos p) i s) (uIcc 0 (longitudDeCuerda i s))).intervalIntegrable
  have h:=intervalIntegral.integral_mono_on len.1 intg intervalIntegrable_const (fun t ht=>bd ht)
  calc
    _ ≤ ∫ _ in (0:ℝ)..longitudDeCuerda i s,M^2 := h
    _ = longitudDeCuerda i s*M^2 := by rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    _ ≤ M^2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right len.2 (sq_nonneg M)

def sueloDiagonalDEF35 : ℝ := 1/(1+techoDEF35^2*techoDEF35^2)

theorem bandas_de_orden_cero_sobre_la_rama {P p x b} (e : EulerFisica P p x b) (xp : 0<x) (half : (x:ℝ)≤1/2)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s) :
    b∈Icc (1/2:ℝ) (techoDEF35^2) ∧ ∀ i : Fin 4,∀ s∈rangoF i,
    if i.val<2 then 1/techoDEF35^2≤camposFisicos p i s ∧ camposFisicos p i s≤techoDEF35
    else sueloDiagonalDEF35≤camposFisicos p i s ∧ camposFisicos p i s≤1 := by
  have d : 0<1-(x:ℝ) := by linarith only [half]
  have v:=bandas_fisicas_de_las_medias e xp d cp pos
  have bm : b≤techoDEF35^2 := v.2.1.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (sub_le_self (1:ℝ) x.coe_nonneg) (sq_nonneg techoDEF35))
  have rc:=banda_puntual_de_las_transversales e xp d cp pos
  have ob:=techo_de_las_oblicuas_fisicas e cp pos
  refine ⟨⟨(by linarith only [half] : (1/2:ℝ)≤1-(x:ℝ)).trans v.1,bm⟩,?_⟩
  intro i s hs
  split_ifs with j
  · exact rc i j s hs
  · have u:=techo_de_la_cavidad_oblicua cp (exp_pos _).le (fun g hg t ht=>(rc g hg t ht).2) ob i j s hs
    have rec:=euler_reciproco_de_la_fibra e cp pos i s hs
    rw [coefLinea,if_neg j] at rec
    exact ⟨banda_oblicua_desde_el_reciproco (pos i s hs) e.coef.le bm u rec,ob i j s hs⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.banda_puntual_de_las_transversales
#print axioms ArticuloA.Historias.techo_de_la_cavidad_oblicua
#print axioms ArticuloA.Historias.bandas_de_orden_cero_sobre_la_rama
