import BandasYTrabajoParaLosReciprocos
import EnergiaDeLaTraslacionFisicaDeFila
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
def constanteTraslacionB33 (x b κ M m : ℝ) :=
  let B:=b*(1/(x+b*κ^2))*M
  let K:=techoDeLosCuatroB33 x b κ M
  let lam:=min (cotaInferiorDensidadB33 x b m κ/2) (κ/5)
  K*(2*B)+K*K*b*(Real.sqrt 3*K^3*(4*B/lam))

theorem control_puntual_de_los_factores_trasladados {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m) (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ))
    (t : ℝ) (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    |Real.exp (logFisicoB33 p x b t i s)-Real.exp (logFisicoB33 p x b 0 i s)|≤
      constanteTraslacionB33 x b κ M m*|t| := by
  let v:=logFisicoB33 p x b
  let K:=techoDeLosCuatroB33 x b κ M
  let B:=b*(1/(x+b*κ^2))*M
  let lam:=min (cotaInferiorDensidadB33 x b m κ/2) (κ/5)
  obtain ⟨pr,cc,dd,aa,pc,_⟩:=bandas_inferiores_de_los_factores h xn bp kp mp cm
  have cap t i:=continuidad_y_techo_de_los_logaritmos h xn bp kp mp cm t i
  have kb : 0≤K := (Real.exp_pos _).le.trans ((cap t i).2 s)
  have bn : 0≤B := (abs_nonneg _).trans ((soporte_de_densidad_extendida h xn bp kp).2 0 0 ⟨le_rfl,zero_le_one⟩)
  have lp : 0<lam := lt_min (by positivity) (by positivity)
  have eqE : (∑ g,energiaDeDiferencias (v t) (v 0) g)=_ :=
    energia_del_articulo_para_la_columna_fija _ _ _ _ t
      (continuidad_del_salto_de_log (nucleo_y_fila_del_perfil h xn bp kp).1 pr t)
      (continuidad_del_salto_de_log (campo_continuo_por_recorte h.continuos 2) (fun s=>kp.trans_le (dd s)) t)
      (continuidad_del_salto_de_log (campo_continuo_por_recorte h.continuos 3) (fun s=>kp.trans_le (aa s)) t)
  have en : Real.sqrt (∑ g,energiaDeDiferencias (v t) (v 0) g)≤4*B/lam*|t| := by
    rw [eqE,div_mul_eq_mul_div,le_div_iff₀ lp]
    exact (mul_comm ..).le.trans (energia_de_la_traslacion_fisica_de_fila h xn bp kp mp cm t)
  let J t:=cavidadFisica (fun g y=>Real.exp (v t g y)) i s
  have cj : |J t-J 0|≤Real.sqrt 3*K^3*(4*B/lam*|t|) :=
    (estimacion_fisica_B35 (fun g=>(cap t g).1.continuousOn) (fun g=>(cap 0 g).1.continuousOn)
      (fun g y _=>(cap t g).2 y) (fun g y _=>(cap 0 g).2 y) i hs).trans
      (mul_le_mul_of_nonneg_left en (by positivity))
  have rs t:=residual_igual_al_producto_por_cavidad pr (fun s=>mp.trans_le (cc s))
    (fun s=>kp.trans_le (dd s)) (fun s=>kp.trans_le (aa s)) t i hs
  have re t: |residualDeTraslacionB33 p x b t i s|≤2*B*|t| := (residual_fisico_de_fila_y_tres_fibras h xn bp kp t).2 i s hs
  have zero: residualDeTraslacionB33 p x b 0 i s=0 := abs_nonpos_iff.mp (by simpa using re 0)
  have base:=rs 0
  rw [zero,add_zero] at base
  have result:=cota_del_factor_desde_la_diferencia_de_cavidades
    (show |Real.exp (v 0 i s)|≤K by rw [abs_of_pos (Real.exp_pos _)]; exact (cap 0 i).2 s)
    (show |Real.exp (v t i s)|≤K by rw [abs_of_pos (Real.exp_pos _)]; exact (cap t i).2 s)
    bp.le base (rs t) (re t) cj
  refine result.trans_eq ?_
  dsimp only [constanteTraslacionB33,B,K,lam]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_puntual_de_los_factores_trasladados
