import R7UniformeParaLaRamaInterior
open Set MeasureTheory Filter Real
open scoped Interval NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

/-- The column uses t-s in D, whereas the row uses s-t. Both intervals lie in [-1,1]. -/
theorem costo_logaritmico_de_una_fibra (D A : ℝ→ℝ) (dc : Continuous D) (ac : Continuous A)
    (dn : 0≤ᵐ[volume.restrict (Ioc (-1:ℝ) 1)] D) (an : 0≤ᵐ[volume.restrict (Ioc (0:ℝ) 2)] A)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (col : Bool) :
    (∫ t in (0:ℝ)..1,D (if col then t-s else s-t)+A (s+t)) ≤
      (∫ t in (-1:ℝ)..1,D t)+(∫ t in (0:ℝ)..2,A t) := by
  have ra : (∫ t in (0:ℝ)..1,A (s+t))≤∫ t in (0:ℝ)..2,A t := by
    rw [intervalIntegral.integral_comp_add_left,add_zero]
    exact intervalIntegral.integral_mono_interval hs.1 (by linarith) (by linarith [hs.2]) an (ac.intervalIntegrable ..)
  have rd : (∫ t in (0:ℝ)..1,D (if col then t-s else s-t))≤∫ t in (-1:ℝ)..1,D t := by
    cases col
    · simp only [Bool.false_eq_true,if_false,intervalIntegral.integral_comp_sub_left,sub_zero]
      exact intervalIntegral.integral_mono_interval (by linarith [hs.1]) (by linarith) hs.2 dn (dc.intervalIntegrable ..)
    · simp only [if_true,sub_eq_add_neg,intervalIntegral.integral_comp_add_right,zero_add]
      exact intervalIntegral.integral_mono_interval (by linarith [hs.2]) (by linarith) (by linarith [hs.1]) dn (dc.intervalIntegrable ..)
  have ct : Continuous (fun t : ℝ=>D (if col then t-s else s-t)) := by
    cases col
    · exact dc.comp (continuous_const.sub continuous_id)
    · exact dc.comp (continuous_id.sub continuous_const)
  have atc : Continuous (fun t : ℝ=>A (s+t)) := ac.comp (continuous_const.add continuous_id)
  rw [intervalIntegral.integral_add (ct.intervalIntegrable (μ:=volume) 0 1) (atc.intervalIntegrable (μ:=volume) 0 1)]
  exact add_le_add rd ra

theorem costo_fisico_de_las_diagonales {P p x b} (e : EulerFisica P p x b) (xp : 0<x)
    (cp : ∀ i,ContinuousOn (camposFisicos p i) (rangoF i)) (pos : ∀ i,∀ s∈rangoF i,0<camposFisicos p i s)
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (col : Bool) :
    (∫ t in (0:ℝ)..1,-log (holguraInteriorR5 p x 2 (if col then t-s else s-t))
      + -log (holguraInteriorR5 p x 3 (s+t))) ≤ masaLogOblicua p x 2+masaLogOblicua p x 3 := by
  let u:=holguraInteriorR5 p x
  have info:=vacancia_fisica_y_logaritmo e xp cp pos
  have c (i : Fin 4) : Continuous (fun t=> -log (u i t)) := ((info i).1.log (fun t=>((info i).2.1 t).ne')).neg
  have nn (i : Fin 4) : (fun _=> (0:ℝ))≤ᵐ[marginalRef i] (fun t=> -log (u i t)) :=
    (info i).2.2.2.2.mono (fun t hi=>neg_nonneg.mpr (log_nonpos ((info i).2.1 t).le hi))
  have z:=costo_logaritmico_de_una_fibra _ _ (c 2) (c 3) (nn 2) (nn 3) s hs col
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2),
    masaLogOblicua,marginalRef,u] using z
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.costo_logaritmico_de_una_fibra
#print axioms ArticuloA.Historias.costo_fisico_de_las_diagonales
