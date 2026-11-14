import DensidadExtendidaDeEuler
import ProyeccionFisicaEnLaFranja
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def terminoLibreB33 (p : FactoresContinuos) (x : ℝ) (i : Fin 3) (s : ℝ) :=
  (if i=0 then x else 1)*campoR15 p (familiaDeFranja i) s

theorem euler_en_la_franja_ampliada {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (i : Fin 3) {s : ℝ} (col : i=0 → s∈unidadCerrada) :
    cargaDeFranja (densidadExteriorB33 p x b) i s+terminoLibreB33 p x i s=1 := by
  by_cases hs : s∈rangoF (familiaDeFranja i)
  · rw [carga_de_franja_con_densidades_iguales (v:=fun z=>b*pesoContinuo p z.1 z.2)
      (fun _ hr _ hc=>densidad_exterior_en_el_cuadrado h hr hc),carga_de_franja_por_escalar,
      carga_en_la_etiqueta_fisica p i hs,terminoLibreB33,campo_dentro_de_su_intervalo _ _ hs]
    have eq:=h.euler (familiaDeFranja i) s hs
    fin_cases i <;> simpa [familiaDeFranja,show ¬(3:Fin 4).val<2 by decide] using eq
  · have di : 2 ≤ (familiaDeFranja i).val := by
      fin_cases i
      · exact (hs (col rfl)).elim
      · decide
      · decide
    have ni : i≠0 := by intro hh; subst i; exact hs (col rfl)
    rw [carga_nula_fuera_de_la_etiqueta _ i hs,terminoLibreB33,if_neg ni,
      campo_diagonal_fuera_de_su_intervalo h _ di hs]; norm_num

def residualDeTraslacionB33 (p : FactoresContinuos) (x b t : ℝ) (i : Fin 4) (s : ℝ) :=
  let U:=densidadExteriorB33 p x b
  let V:=fun z : ℝ×ℝ=>U (z.1+t,z.2)
  match i with
  | 0=>(∫ c in (0:ℝ)..1,V (s,c))+x*filaExteriorB33 p x b (s+t)-1
  | 1=>cargaDeFranja V 0 s+terminoLibreB33 p x 0 s-1
  | 2=>cargaDeFranja V 1 s+terminoLibreB33 p x 1 (s+t)-1
  | 3=>cargaDeFranja V 2 s+terminoLibreB33 p x 2 (s+t)-1

theorem residual_fisico_de_fila_y_tres_fibras {p x b κ M} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (t : ℝ) :
    (∀ s,residualDeTraslacionB33 p x b t 0 s=0) ∧
    ∀ i,∀ s∈rangoF i,|residualDeTraslacionB33 p x b t i s|≤2*(b*(1/(x+b*κ^2))*M)*|t| := by
  have z s : residualDeTraslacionB33 p x b t 0 s=0 := sub_eq_zero.mpr (ecuacion_de_la_fila_en_toda_la_recta h xn bp kp (s+t))
  have cap:=soporte_de_densidad_extendida h xn bp kp
  let B:=b*(1/(x+b*κ^2))*M
  have bn : 0≤B := (abs_nonneg _).trans (cap.2 0 0 ⟨le_rfl,zero_le_one⟩)
  have bound (i : Fin 3) (s : ℝ) (hs : i=0 → s∈unidadCerrada) :
      |cargaDeFranja (fun z=>(densidadExteriorB33 p x b) (z.1+t,z.2)) i s+
        terminoLibreB33 p x i (etiquetaTrasladada i s t)-1|≤2*B*|t| := by
    have bound:=residual_de_fila_en_las_tres_fibras _ cap.1.measurable bn cap.2 i s t
    have e:=euler_en_la_franja_ampliada h i (s:=etiquetaTrasladada i s t) (fun hi=>by
      simpa [etiquetaTrasladada,hi] using hs hi)
    change |cargaDeFranja _ i s-cargaDeFranja _ i (etiquetaTrasladada i s t)|≤_ at bound
    convert bound using 2; linarith only [e]
  refine ⟨z,?_⟩
  intro i s hs
  fin_cases i
  · change |residualDeTraslacionB33 p x b t 0 s|≤_
    rw [z s,abs_zero]; exact mul_nonneg (mul_nonneg (by norm_num) bn) (abs_nonneg _)
  · exact bound 0 s (fun _=>hs)
  · exact bound 1 s (fun hh=>False.elim ((by decide : (1:Fin 3)≠0) hh))
  · exact bound 2 s (fun hh=>False.elim ((by decide : (2:Fin 3)≠0) hh))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_en_la_franja_ampliada
#print axioms ArticuloA.Historias.residual_fisico_de_fila_y_tres_fibras
