import SustitucionDeVacanciasEnLaInversa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
def mediaExterior {n} (g : Cell n→ℝ) := (∑ z,g z)/(n:ℝ)^2
def perfilDirectoSinFiltro {n} (j : ℕ) (p : FactoresContinuos) (z : Cell n) := sumaSinFiltro j p z/(n:ℝ)

theorem reduccion_a_la_media_exterior {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margin : 2*(C:ℝ)≤κ*n) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W) :
    |blancoInverso h p w 1/(n:ℝ)^2-(n*escalaDeLasFuentes n h p)*
      mediaExterior (fun z => w z*productoRCEnElCentro p z*perfilDirectoSinFiltro h p z)|≤
    (4*W*((m:ℝ)^4/κ^4)^2+W*(1+(m:ℝ))*C)/n := by
  have np : 0<n := by omega
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have eq : n*escalaDeLasFuentes n h p*mediaExterior
      (fun z => w z*productoRCEnElCentro p z*perfilDirectoSinFiltro h p z)=
      sumaInversaDeLosCentros h p w/(n:ℝ)^2 := by
    rw [suma_inversa_por_cruces np]; unfold mediaExterior perfilDirectoSinFiltro
    simp_rw [←mul_div_assoc]; rw [←Finset.sum_div]; field_simp; ring
  rw [eq,←sub_div,abs_div,abs_of_pos (pow_pos nr 2)]
  apply (div_le_div_of_nonneg_right (eliminar_filtro_y_reemplazar_vacancias hn sp kp bal margin w wp cap)
    (sq_nonneg (n:ℝ))).trans_eq
  field_simp; ring

theorem continuidad_de_la_media_exterior {n} (g f : Cell n→ℝ) (d : ℝ) (dp : 0≤d)
    (close : ∀ z,|g z-f z|≤d) : |mediaExterior g-mediaExterior f|≤d := by
  unfold mediaExterior
  rw [←sub_div,abs_div,abs_of_nonneg (sq_nonneg (n:ℝ)),←Finset.sum_sub_distrib]
  by_cases h : n=0
  · simp [h,dp]
  have nr : 0<(n:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero h)
  apply (div_le_iff₀ (pow_pos nr 2)).mpr
  apply (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun z _ => close z)).trans_eq _)
  simp [Cell,Fintype.card_prod,nsmul_eq_mul]; ring

theorem media_del_producto_de_filas_y_columnas {n} (p : FactoresContinuos) :
    mediaExterior (productoRCEnElCentro (n:=n) p)=
      ((∑ i : Fin n,(p.fila (medio n i.val):ℝ))/n)*((∑ j : Fin n,(p.columna (medio n j.val):ℝ))/n) := by
  unfold mediaExterior productoRCEnElCentro
  rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum]; rw [←Finset.sum_mul]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reduccion_a_la_media_exterior
#print axioms ArticuloA.Historias.continuidad_de_la_media_exterior
#print axioms ArticuloA.Historias.media_del_producto_de_filas_y_columnas
