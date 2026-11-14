import VacanciasBorelYSeccionesDelDual
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def seccionDelDual {H : ℝ} (u : CajaDual H) (i : Fin 4) (s : ℝ) :=
  cavidadFisica (vacanciaDeCampo (campoDual u)) i (recorte i s)

theorem seccion_del_dual_continua {H : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4) : Continuous (seccionDelDual u i) := by
  have b:=vacancia_de_campo_en_unidad (campo_dual_acotado hp u)
  have c:=cavidad_continua_para_campos_medibles _ (vacancia_de_campo_integrable (campo_dual_medible u) (campo_dual_acotado hp u))
    (vacancia_de_campo_medible (campo_dual_medible u)) 1 (fun j s=>(abs_of_nonneg (b j s).1).le.trans (b j s).2) i
  exact c.comp_continuous (continuous_const.min (continuous_const.max continuous_id)) (recorte_dentro i)

theorem seccion_del_dual_en_unidad {H : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4) (s : ℝ) : seccionDelDual u i s∈Icc 0 1 := by
  let f:=vacanciaDeCampo (campoDual u)
  let t:=recorte i s
  have b:=vacancia_de_campo_en_unidad (campo_dual_acotado hp u)
  have l:=longitud_en_unidad i (recorte_dentro i s)
  have box r : productoEnCuerda f i t r∈Icc 0 1 := by
    have join {y z : ℝ} (hy : y∈Icc 0 1) (hz : z∈Icc 0 1) : y*z∈Icc 0 1 :=
      ⟨mul_nonneg hy.1 hz.1,mul_le_one₀ hy.2 hz.1 hz.2⟩
    exact join (join (b _ _) (b _ _)) (b _ _)
  refine ⟨intervalIntegral.integral_nonneg l.1 (fun r _=>(box r).1),?_⟩
  have bd:=intervalIntegral.norm_integral_le_of_norm_le_const (f:=productoEnCuerda f i t) (a:=0) (b:=longitudDeCuerda i t)
    (fun r _=>by rw [Real.norm_eq_abs,abs_of_nonneg (box r).1]; exact (box r).2)
  apply (le_abs_self _).trans; apply bd.trans
  simpa only [t,sub_zero,abs_of_nonneg l.1,one_mul] using l.2

theorem partida_con_un_potencial {H : ℝ} (u : CajaDual H) (i : Fin 4) {g : Fin 4→ℝ→ℝ}
    (gm : ∀ j,Measurable (g j)) (gb : ∀ j s,g j s∈Icc 0 H) (v : CajaDual H)
    (eq : ∀ j,campoDual v j=ᵐ[marginalRef j] g j) (fix : ∀ j,j≠i → g j=campoDual u j) :
    particionDual v=∫ s,exp (-g i s)*seccionDelDual u i s ∂marginalRef i := by
  rw [particion_en_una_fibra v gm gb eq i]; apply integral_congr_ae; filter_upwards [linea_en_dominio i] with s hs
  rw [seccionDelDual,recorte_fijo i hs,misma_cavidad_fuera_de_una_etiqueta i fix]

theorem competidor_de_una_linea {H : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4) {w : ℝ→ℝ}
    (wm : Measurable w) (wb : ∀ s,w s∈Icc 0 H) :
    ∃ v : CajaDual H,(∀ j,j≠i → costoDual v j=costoDual u j) ∧
      costoDual v i=(∫ s,potencialDeHolgura (w s) ∂marginalRef i) ∧
      particionDual v=∫ s,exp (-w s)*seccionDelDual u i s ∂marginalRef i := by
  let g (j : Fin 4):=if j=i then w else campoDual u j
  have gm j : Measurable (g j) := by by_cases h : j=i <;> simp [g,h,wm,campo_dual_medible]
  have gb j s : g j s∈Icc 0 H := by by_cases h : j=i <;> simp [g,h,wb,campo_dual_acotado hp]
  obtain ⟨v,eq⟩:=competidor_de_campos_borel g gm gb
  have same j (h : j≠i) : g j=campoDual u j := if_neg h
  have c j : costoDual v j=∫ s,potencialDeHolgura (g j s) ∂marginalRef j := integral_congr_ae
    ((eq j).fun_comp potencialDeHolgura)
  exact ⟨v,fun j h=>by simpa only [same j h,costoDual] using c j,by simpa [g] using c i,
    by simpa [g] using partida_con_un_potencial u i gm gb v eq same⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.seccion_del_dual_continua
#print axioms ArticuloA.Historias.seccion_del_dual_en_unidad
#print axioms ArticuloA.Historias.partida_con_un_potencial
#print axioms ArticuloA.Historias.competidor_de_una_linea
