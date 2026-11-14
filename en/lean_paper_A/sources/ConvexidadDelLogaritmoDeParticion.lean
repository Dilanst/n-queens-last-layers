import ConvexidadFuerteDelPotencialDeHolgura
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
private theorem exponencial_en_el_punto_medio (u v : ℝ) :
    exp ((u+v)/2)≤(exp u+exp v)/2 := by
  have aux y : exp (y/2)^2=exp y := by rw [sq,←exp_add]; congr 1; ring
  have m : exp ((u+v)/2)=exp (u/2)*exp (v/2) := by rw [←exp_add]; congr 1; ring
  rw [m,←aux u,←aux v]; nlinarith only [sq_nonneg (exp (u/2)-exp (v/2))]

theorem convexidad_de_log_particion_por_punto_medio {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : α→ℝ) (fi : Integrable (fun z=>exp (F z)) μ) (gi : Integrable (fun z=>exp (G z)) μ)
    (mi : Integrable (fun z=>exp ((F z+G z)/2)) μ)
    (fp : 0<∫ z,exp (F z) ∂μ) (gp : 0<∫ z,exp (G z) ∂μ) (mp : 0<∫ z,exp ((F z+G z)/2) ∂μ) :
    log (∫ z,exp ((F z+G z)/2) ∂μ)≤(log (∫ z,exp (F z) ∂μ)+log (∫ z,exp (G z) ∂μ))/2 := by
  let a:=∫ z,exp (F z) ∂μ
  let b:=∫ z,exp (G z) ∂μ
  let c:=exp ((log a+log b)/2)
  have cp : 0<c := exp_pos _
  have point z : exp ((F z+G z)/2)/c ≤ (exp (F z)/a+exp (G z)/b)/2 := by
    have mid:=exponencial_en_el_punto_medio (F z-log a) (G z-log b)
    rw [show ((F z-log a)+(G z-log b))/2=(F z+G z)/2-(log a+log b)/2 by ring,
      exp_sub,exp_sub,exp_sub,exp_log fp,exp_log gp] at mid
    exact mid
  have comparison:=integral_mono (mi.div_const c) (((fi.div_const a).add (gi.div_const b)).div_const 2) point
  change (∫ z,exp ((F z+G z)/2)/c ∂μ) ≤ ∫ z,(exp (F z)/a+exp (G z)/b)/2 ∂μ at comparison
  rw [integral_div,integral_div,integral_add (fi.div_const a) (gi.div_const b),integral_div,integral_div] at comparison
  change (∫ z,exp ((F z+G z)/2) ∂μ)/c ≤ (a/a+b/b)/2 at comparison
  rw [div_self fp.ne',div_self gp.ne'] at comparison
  have le : (∫ z,exp ((F z+G z)/2) ∂μ)≤c := (div_le_one cp).mp (by linarith)
  exact (Real.log_le_log mp le).trans_eq (log_exp _)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.convexidad_de_log_particion_por_punto_medio
