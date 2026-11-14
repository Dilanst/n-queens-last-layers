import DeLosResiduosALaNormaAnclada
import ResiduosDeLaDiferenciaDeDensidades
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
/-- Row-translation energy estimate for the actual solution of Euler, with an anchored column.
    On each diagonal interval the norm uses Lebesgue measure of mass two. -/
theorem energia_de_la_traslacion_fisica_de_fila {p x b κ M m} (h : DatosTraslacionFisica p x b κ M)
    (xn : 0≤x) (bp : 0<b) (kp : 0<κ) (mp : 0<m)
    (cm : ∀ s∈unidadCerrada,m≤(p.columna s:ℝ)) (t : ℝ) :
    let r:=saltoLogB33 (filaExteriorB33 p x b) t
    let d:=saltoLogB33 (campoR15 p 2) t
    let a:=saltoLogB33 (campoR15 p 3) t
    min (cotaInferiorDensidadB33 x b m κ/2) (κ/5)*Real.sqrt (energiaRealB34 r d a)≤
      4*(b*(1/(x+b*κ^2))*M)*|t| := by
  intro r d a
  let U:=densidadExteriorB33 p x b
  let V:=trasladaFilaB33 U t
  let D:=campoR15 p 2
  let A:=campoR15 p 3
  let Dt:=fun s=>D (s+t)
  let At:=fun s=>A (s+t)
  obtain ⟨pr,cc,dd,aa,pc,bd⟩:=bandas_inferiores_de_los_factores h xn bp kp mp cm
  have uc : Continuous U := (soporte_de_densidad_extendida h xn bp kp).1
  have vc : Continuous V := continuidad_de_la_densidad_trasladada uc t
  have dc : Continuous D := campo_continuo_por_recorte h.continuos 2
  have ac : Continuous A := campo_continuo_por_recorte h.continuos 3
  have rc : Continuous r := continuidad_del_salto_de_log (nucleo_y_fila_del_perfil h xn bp kp).1 pr t
  have cd : Continuous d := continuidad_del_salto_de_log dc (fun s=>kp.trans_le (dd s)) t
  have ca : Continuous a := continuidad_del_salto_de_log ac (fun s=>kp.trans_le (aa s)) t
  have dtc : Continuous Dt := dc.comp (continuous_id.add continuous_const)
  have atc : Continuous At := ac.comp (continuous_id.add continuous_const)
  have eqD s : Real.log (D s)+d s=Real.log (Dt s) := by dsimp [d,D,Dt,saltoLogB33]; ring
  have eqA s : Real.log (A s)+a s=Real.log (At s) := by dsimp [a,A,At,saltoLogB33]; ring
  have work:=coercividad_entre_densidades_positivas pc kp uc vc dc dtc ac atc rc cd ca
    (fun z=>⟨bd z,bd (z.1+t,z.2)⟩) (fun s=>⟨dd s,dd (s+t)⟩) (fun s=>⟨aa s,aa (s+t)⟩)
    (identidad_logaritmica_de_la_densidad bp pr (fun s=>mp.trans_le (cc s)) (fun s=>kp.trans_le (dd s))
      (fun s=>kp.trans_le (aa s)) t) eqD eqA
  let B:=b*(1/(x+b*κ^2))*M
  have nn : 0≤B := (abs_nonneg _).trans ((soporte_de_densidad_extendida h xn bp kp).2 0 0 ⟨le_rfl,zero_le_one⟩)
  have lp : 0<min (cotaInferiorDensidadB33 x b m κ/2) (κ/5) := lt_min (by positivity) (by positivity)
  have est:=ganancia_anclada_por_dos_residuos (U:=fun z=>V z-U z) (D:=fun s=>Dt s-D s)
    (A:=fun s=>At s-A s) (Z:=2*B*|t|) (vc.sub uc) rc cd ca (dtc.sub dc) (atc.sub ac) lp
    (mul_nonneg (mul_nonneg (by norm_num) nn) (abs_nonneg _)) work
    (fun s _=>diferencia_de_las_ecuaciones_de_fila h xn bp kp t s)
    (fun _ hs=>diferencia_de_las_ecuaciones_oblicuas h xn bp kp t 1 (by decide) hs)
    (fun _ hs=>diferencia_de_las_ecuaciones_oblicuas h xn bp kp t 2 (by decide) hs)
  change _≤4*B*|t|
  linarith only [est]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.energia_de_la_traslacion_fisica_de_fila
