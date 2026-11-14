import AdjuncionDeLaDensidadTrasladada
import EulerDeTraslacionDesdeLasMarginales
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Interval
def pesoDePruebaB33 (p : FactoresContinuos) (b : ℝ) (z : ℝ×ℝ) :=
  b*campoR15 p 0 z.1*campoR15 p 1 z.2*campoR15 p 2 (z.1-z.2)*campoR15 p 3 (z.1+z.2)

theorem probar_integrales_fisicas_continuas {p : FactoresContinuos} (b : ℝ)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (i : Fin 4) (w : ℝ→ℝ) (wc : Continuous w) :
    (∫ z,b*pesoContinuo p z.1 z.2*w (coord i z) ∂cuadrado)=
    ∫ s,b*integralFisica p i s*w s ∂marginalRef i := by
  let U:=pesoDePruebaB33 p b
  have cc:=campo_continuo_por_recorte cp
  have uc : Continuous U := (((continuous_const.mul ((cc 0).comp continuous_fst)).mul ((cc 1).comp continuous_snd)).mul
    ((cc 2).comp (continuous_fst.sub continuous_snd))).mul ((cc 3).comp (continuous_fst.add continuous_snd))
  have phys r (hr : r∈unidadCerrada) c (hc : c∈unidadCerrada) : U (r,c)=b*pesoContinuo p r c := by
    obtain ⟨d,a⟩:=dominios r c hr hc
    dsimp only [U,pesoDePruebaB33]
    rw [campo_dentro_de_su_intervalo p 0 hr,campo_dentro_de_su_intervalo p 1 hc,
      campo_dentro_de_su_intervalo p 2 d,campo_dentro_de_su_intervalo p 3 a]
    dsimp [pesoContinuo,camposFisicos,factorF]; ring
  have eq : (∫ z,U z*w (coord i z) ∂cuadrado)=(∫ z,b*pesoContinuo p z.1 z.2*w (coord i z) ∂cuadrado) := by
    apply integral_congr_ae; filter_upwards [tablero_en_dominio] with z hz; rw [←phys _ hz.1 _ hz.2]
  rw [←eq]
  have proj (j : Fin 3) {s : ℝ} (hs : s∈rangoF (familiaDeFranja j)) :
      cargaDeFranja U j s=b*integralFisica p (familiaDeFranja j) s := by
    rw [carga_de_franja_con_densidades_iguales (v:=fun z=>b*pesoContinuo p z.1 z.2) phys,carga_de_franja_por_escalar,carga_en_la_etiqueta_fisica p j hs]
  have ob (a : Bool) : (∫ z,U z*w (coord (indiceDeLaSeccion a) z) ∂cuadrado)=
      ∫ s,b*integralFisica p (indiceDeLaSeccion a) s*w s ∂marginalRef (indiceDeLaSeccion a) := by
    rw [adjuncion_de_diagonal_extendida U w uc wc a]
    have ref : marginalRef (indiceDeLaSeccion a)=(if a then anti else diag) := by
      cases a <;> exact Measure.restrict_congr_set Ioc_ae_eq_Icc
    rw [←ref]; apply integral_congr_ae; filter_upwards [linea_en_dominio (indiceDeLaSeccion a)] with s hs
    cases a
    · exact congrArg (·*w s) (proj 1 hs)
    · exact congrArg (·*w s) (proj 2 hs)
  fin_cases i
  · change (∫ z,U z*w z.1 ∂cuadrado)=_
    rw [adjuncion_de_fila_extendida U w uc wc,←show marginalRef 0=unidad from Measure.restrict_congr_set Ioc_ae_eq_Icc]
    apply integral_congr_ae; filter_upwards [linea_en_dominio 0] with s hs
    apply congrArg (·*w s)
    change _=b*(∫ c in (0:ℝ)..1,pesoContinuo p s c)
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun c hc=>phys s hs c (by simpa only [unidadCerrada,uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hc))
  · have rev := integral_prod_swap (μ:=unidad) (ν:=unidad) (fun z : ℝ×ℝ=>U z*w z.2)
    change (∫ z,U z*w z.2 ∂cuadrado)=_
    change (∫ z,U z.swap*w z.1 ∂cuadrado)=(∫ z,U z*w z.2 ∂cuadrado) at rev
    rw [←rev]
    rw [adjuncion_de_fila_extendida (fun z=>U z.swap) w (uc.comp continuous_swap) wc,
      ←show marginalRef 1=unidad from Measure.restrict_congr_set Ioc_ae_eq_Icc]
    apply integral_congr_ae; filter_upwards [linea_en_dominio 1] with s hs
    apply congrArg (·*w s)
    change _=b*(∫ r in (0:ℝ)..1,pesoContinuo p r s)
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun r hr=>phys r (by simpa only [unidadCerrada,uIcc_of_le (zero_le_one : (0:ℝ)≤1)] using hr) s hs)
  · exact ob false
  · exact ob true
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.probar_integrales_fisicas_continuas
