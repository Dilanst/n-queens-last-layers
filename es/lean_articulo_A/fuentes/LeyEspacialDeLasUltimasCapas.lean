import CentroInversoDeLaMedidaDeLosHuecos
import PromedioDeLosCrucesPorDobleCuenta
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Set Perfil Limites
open scoped Topology
/-- Section 9(b): weak convergence of the expectation of the spatial measure of
empty crosses. The function may have either sign; h is fixed before n tends to infinity. -/
theorem ley_espacial_media_de_los_cruces {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0)))
    (h : ℕ) (hh : 0<h) (t : ℝ×ℝ→ℝ) (ct : ContinuousOn t cuadradoCerrado) :
    Tendsto (fun n : ℕ => promedioNivel n (n-h) (fun Q => mediaCruces Q h (valorEnCentro t)))
      atTop (𝓝 (integralDeLosHuecos (p 0) t)) := by
  obtain ⟨T₀,cap₀⟩:=(isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn ct
  let T:=|T₀|+1
  have tp : 0<T := by dsimp [T]; positivity
  have bound (x : ℝ) (hx : x∈unidadCerrada) (y : ℝ) (hy : y∈unidadCerrada) : |t (x,y)|≤T := by
    exact (cap₀ (x,y) ⟨hx,hy⟩).trans ((le_abs_self _).trans (by dsimp [T]; linarith))
  let w:=fun (n : ℕ) (z : Cell n) => valorEnCentro t z/aDelLleno p b z
  have bz : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bp:=(rama.euler 0 bz).coef
  have mp:=mul_pos bp (pow_pos rama.kp 8)
  have cap n (z : Cell n) : |w n z|≤T/(b 0*κ^8) := by
    have lo:=piso_integral_del_cruce (rama.espacio 0 bz) rama.kp rama.lp bp
      (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
    change b 0*κ^8≤aDelLleno p b z at lo
    dsimp only [w]; rw [abs_div,abs_of_pos (mp.trans_le lo)]
    exact div_le_div₀ tp.le (bound _ (medio_admisible z.1.isLt) _ (medio_admisible z.2.isLt)) mp lo
  have inv:=inversa_con_centro_convergente rama first h hh w (div_nonneg tp.le mp.le) cap
    (centro_del_test_continuo rama cont (h-1) t ct tp.le bound)
  apply estructura_en_media h hh.ne' w _ bp
    ((niveles_de_una_reparacion first h hh).mono (fun _ H => ⟨H.1.ne',H.2.ne'⟩))
  · simpa only [fraccionDelPerfil,sub_zero] using (conclusiones_de_capas_fijas rama cont first h).2.1 h hh le_rfl
  · exact inv.2
  · exact reponderacion_de_una_prueba_acotada rama cont first h hh _ T tp
      (fun _ z => bound _ (medio_admisible z.1.isLt) _ (medio_admisible z.2.isLt))
/-- A test defined only on the closed board also suffices. -/
def pruebaEnElTablero (t : cuadradoCerrado→ℝ) (z : ℝ×ℝ) : ℝ := if hz : z∈cuadradoCerrado then t ⟨z,hz⟩ else 0

theorem ley_para_una_prueba_en_el_cuadrado {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0)))
    (h : ℕ) (hh : 0<h) (t : cuadradoCerrado→ℝ) (ct : Continuous t) :
    Tendsto (fun n : ℕ => promedioNivel n (n-h) (fun Q => mediaCruces Q h (fun z =>
      t ⟨(medio n z.1.val,medio n z.2.val),medio_admisible z.1.isLt,medio_admisible z.2.isLt⟩)))
      atTop (𝓝 (integralDeLosHuecos (p 0) (pruebaEnElTablero t))) := by
  have hc : ContinuousOn (pruebaEnElTablero t) cuadradoCerrado := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun z : cuadradoCerrado => pruebaEnElTablero t z.val)
    have eq : (fun z : cuadradoCerrado => pruebaEnElTablero t z.val)=t := by
      funext z; unfold pruebaEnElTablero; rw [dif_pos z.property]
    rw [eq]; exact ct
  have e:=ley_espacial_media_de_los_cruces rama cont first h hh (pruebaEnElTablero t) hc
  apply e.congr; intro n
  have domain (z : Cell n) : (medio n z.1.val,medio n z.2.val)∈cuadradoCerrado :=
    ⟨medio_admisible z.1.isLt,medio_admisible z.2.isLt⟩
  have eq : (valorEnCentro (n:=n) (pruebaEnElTablero t))=fun z : Cell n =>
      t ⟨(medio n z.1.val,medio n z.2.val),domain z⟩ := by
    funext z; unfold valorEnCentro pruebaEnElTablero; rw [dif_pos (domain z)]
  rw [eq]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.ley_espacial_media_de_los_cruces
#print axioms ArticuloA.Historias.ley_para_una_prueba_en_el_cuadrado
