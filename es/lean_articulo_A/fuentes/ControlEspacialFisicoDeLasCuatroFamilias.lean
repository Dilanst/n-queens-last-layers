import RegularidadDeLosFactoresPorTraslacion
import TrasposicionDeLasEcuacionesFisicas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
theorem oscilacion_de_las_tres_familias_movidas {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m) (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ))
    (i : Fin 4) (active : i≠1) {u v : ℝ} (hu : u∈rangoF i) (hv : v∈rangoF i) :
    |camposFisicos p i u-camposFisicos p i v|≤constanteTraslacionB33 x b κ M m*|u-v| := by
  have res:=control_puntual_de_los_factores_trasladados h xn bp kp mp cm (u-v) i hv
  obtain ⟨pr,_,dd,aa,_,_⟩:=bandas_inferiores_de_los_factores h xn bp kp mp cm
  have idx : v+(u-v)=u := by ring
  fin_cases i
  · change |Real.exp (Real.log (filaExteriorB33 p x b (v+(u-v))))-Real.exp (Real.log (filaExteriorB33 p x b (v+0)))|≤_ at res
    rw [idx,add_zero,Real.exp_log (pr _),Real.exp_log (pr _),fila_por_euler_coincide_en_el_tablero h hu,
      fila_por_euler_coincide_en_el_tablero h hv] at res; exact res
  · exact (active rfl).elim
  · change |Real.exp (Real.log (campoR15 p 2 (v+(u-v))))-Real.exp (Real.log (campoR15 p 2 (v+0)))|≤_ at res
    rw [idx,add_zero,Real.exp_log (kp.trans_le (dd _)),Real.exp_log (kp.trans_le (dd _)),
      campo_dentro_de_su_intervalo p 2 hu,campo_dentro_de_su_intervalo p 2 hv] at res; exact res
  · change |Real.exp (Real.log (campoR15 p 3 (v+(u-v))))-Real.exp (Real.log (campoR15 p 3 (v+0)))|≤_ at res
    rw [idx,add_zero,Real.exp_log (kp.trans_le (aa _)),Real.exp_log (kp.trans_le (aa _)),
      campo_dentro_de_su_intervalo p 3 hu,campo_dentro_de_su_intervalo p 3 hv] at res; exact res

theorem control_espacial_por_euler_y_bandas {p x b κ M m L} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m) (mm : 1≤M)
    (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ)) (row : ∀ s∈unidadCerrada,m≤(p.fila s:ℝ) ∧ (p.fila s:ℝ)≤M)
    (mass : (∫ s in (0:ℝ)..1,(p.fila s:ℝ))=1) (common : constanteTraslacionB33 x b κ M m≤L) :
    ControlEspacial p (min m κ) M L := by
  have ht:=datos_fisicos_del_traspuesto h (fun s hs=>(row s hs).2) mass
  have osc i (hi : i≠1) {u v : ℝ} (hu : u∈rangoF i) (hv : v∈rangoF i) :=
    (oscilacion_de_las_tres_familias_movidas h xn bp kp mp cm i hi hu hv).trans (mul_le_mul_of_nonneg_right common (abs_nonneg _))
  refine ⟨⟨fun s hs=>(min_le_left ..).trans (row s hs).1,fun _ hu _ hv=>osc 0 (by decide) hu hv⟩,
    ⟨fun s hs=>(min_le_left ..).trans (cm s hs),?_⟩,
    ⟨fun s hs=>(min_le_right ..).trans (h.diagonal 2 (by decide) s hs).1,fun _ hu _ hv=>osc 2 (by decide) hu hv⟩,
    ⟨fun s hs=>(min_le_right ..).trans (h.diagonal 3 (by decide) s hs).1,fun _ hu _ hv=>osc 3 (by decide) hu hv⟩,
    fun s hs=>(row s hs).2,h.columna,fun s hs=>(h.diagonal 2 (by decide) s hs).2.trans mm,
    fun s hs=>(h.diagonal 3 (by decide) s hs).2.trans mm⟩
  intro u hu v hv
  exact (oscilacion_de_las_tres_familias_movidas ht xn bp kp mp (fun s hs=>(row s hs).1) 0
    (by decide) hu hv).trans (mul_le_mul_of_nonneg_right common (abs_nonneg _))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscilacion_de_las_tres_familias_movidas
#print axioms ArticuloA.Historias.control_espacial_por_euler_y_bandas
