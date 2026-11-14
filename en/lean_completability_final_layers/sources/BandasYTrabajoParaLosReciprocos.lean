import CavidadesDeLosFactoresTrasladados
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
theorem cota_del_factor_desde_la_diferencia_de_cavidades {y yt d b j jt e K H W : ℝ}
    (hy : |y|≤K) (hyt : |yt|≤K) (bn : 0≤b)
    (base : y*(d+b*j)=1) (res : yt*(d+b*jt)=1+e) (be : |e|≤W) (bj : |jt-j|≤H) :
    |yt-y|≤K*W+K*K*b*H := by
  have kn : 0≤K := (abs_nonneg y).trans hy
  have eq : yt-y=y*e-y*yt*b*(jt-j) := by
    linear_combination y*res-yt*base
  rw [eq]
  apply (abs_sub ..).trans
  rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg bn]
  exact add_le_add (mul_le_mul hy be (abs_nonneg _) kn)
    (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hy hyt (abs_nonneg _) kn) bn) bj
       (abs_nonneg _) (by positivity))

def techoDeLosCuatroB33 (x b κ M : ℝ) := max (1/(x+b*κ^2)) (max M 1)

theorem continuidad_y_techo_de_los_logaritmos {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m) (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ))
    (t : ℝ) (i : Fin 4) :
    Continuous (logFisicoB33 p x b t i) ∧ ∀ s,Real.exp (logFisicoB33 p x b t i s)≤techoDeLosCuatroB33 x b κ M := by
  obtain ⟨pr,cc,dd,aa,_,_⟩:=bandas_inferiores_de_los_factores h xn bp kp mp cm
  have base:=campo_continuo_por_recorte h.continuos
  have tr : Continuous (fun y : ℝ=>y+t) := continuous_id.add continuous_const
  have rr:=nucleo_y_fila_del_perfil h xn bp kp
  have lr : Continuous (fun s=>Real.log (filaExteriorB33 p x b s)) := rr.1.log (fun s=>(pr s).ne')
  have lc:= (base 1).log (fun s=>(mp.trans_le (cc s)).ne')
  have ld:= (base 2).log (fun s=>(kp.trans_le (dd s)).ne')
  have la:= (base 3).log (fun s=>(kp.trans_le (aa s)).ne')
  have topC : M≤techoDeLosCuatroB33 x b κ M := (le_max_left ..).trans (le_max_right ..)
  have topD : 1≤techoDeLosCuatroB33 x b κ M := (le_max_right ..).trans (le_max_right ..)
  fin_cases i
  · refine ⟨lr.comp tr,fun s=>?_⟩
    change Real.exp (Real.log (filaExteriorB33 p x b (s+t)))≤_
    rw [Real.exp_log (pr _)]; exact (rr.2 _).2.1.trans (le_max_left ..)
  · refine ⟨lc,fun s=>?_⟩
    change Real.exp (Real.log (campoR15 p 1 s))≤_; rw [Real.exp_log (mp.trans_le (cc _))]
    exact (h.columna _ (recorte_dentro 1 s)).trans topC
  · refine ⟨ld.comp tr,fun s=>?_⟩
    change Real.exp (Real.log (campoR15 p 2 (s+t)))≤_; rw [Real.exp_log (kp.trans_le (dd _))]
    exact (h.diagonal 2 (by decide) _ (recorte_dentro 2 (s+t))).2.trans topD
  · refine ⟨la.comp tr,fun s=>?_⟩
    change Real.exp (Real.log (campoR15 p 3 (s+t)))≤_; rw [Real.exp_log (kp.trans_le (aa _))]
    exact (h.diagonal 3 (by decide) _ (recorte_dentro 3 (s+t))).2.trans topD
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_del_factor_desde_la_diferencia_de_cavidades
#print axioms ArticuloA.Historias.continuidad_y_techo_de_los_logaritmos
