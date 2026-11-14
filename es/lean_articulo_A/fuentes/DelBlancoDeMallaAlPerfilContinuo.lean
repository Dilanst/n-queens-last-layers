import DescarteYProductoBajoLaMasaReal
import CocienteDeCuadraturasDelCruce
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 RealFinita
noncomputable section

theorem probabilidad_fisica_por_peso {n h} (p : FactoresContinuos) (np : 0<n) (e : Cell n) :
    (probDeLaCasilla h p e:ℝ)=((↑(n-h):ℝ)/Wfisico n p)*pesoFisico n p e := by
  unfold probDeLaCasilla probArista cuotaR totalIni
  simp only [NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_mul,NNReal.coe_pow,masa_cuando_empieza,peso_para_el_nucleo]
  have nz : (n:ℝ)≠0 := by exact_mod_cast np.ne'
  by_cases no : Wfisico n p=0
  · simp [no]
  · field_simp; ring

theorem suma_sin_filtro_como_cociente {n h} (p : FactoresContinuos) (np : 0<n) (z : Cell n) :
    sumaSinFiltro h p z/(n:ℝ)=(↑(n-h):ℝ)/n*
      (sumaDeNumerador n p (medio n z.1.val) (medio n z.2.val)/Wfisico n p) := by
  unfold sumaSinFiltro sumaDeNumerador
  simp_rw [probabilidad_fisica_por_peso p np,mul_assoc]
  rw [←Finset.mul_sum]
  change (((↑(n-h):ℝ)/Wfisico n p)*(∑ e : Cell n,integrandoDirecto p _ _ _ _))/(n:ℝ)=_
  ring

/-- Uniform in the position of the empty cross. The continuum integrand here
uses the factors at the SAME density as the mesh, also for fixed positive h. -/
theorem malla_al_continuo_en_la_misma_densidad {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L b : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (lp : 0≤L) (bp : 0<b)
    (bal : BalanceMalla n h p C) (margen : 2*(C:ℝ)≤κ*n)
    (masa : integralTablero (pesoContinuo p)=((↑(n-h):ℝ)/n)/b) (z : Cell n) :
    |blancoNormalizado h p z-perfilDirectoContinuo p b (medio n z.1.val) (medio n z.2.val)|≤
      (4*(m:ℝ)^3*C+4*((m:ℝ)^4/κ^4)*(m:ℝ)^4+
        b*(2*(4*(m:ℝ)^3*L)*(m:ℝ)^4+2*(8*(m:ℝ)^7*L)))/(n:ℝ) := by
  have np : 0<n := by omega
  have nr : 0<(n:ℝ) := by exact_mod_cast np
  have geom:=error_del_descarte_y_producto hn sp kp m1 bal margen z
  have normed : |blancoNormalizado h p z-sumaSinFiltro h p z/(n:ℝ)|≤
      (4*(m:ℝ)^3*C+4*((m:ℝ)^4/κ^4)*(m:ℝ)^4)/(n:ℝ) := by
    unfold blancoNormalizado; rw [←sub_div,abs_div,abs_of_pos nr]
    exact div_le_div_of_nonneg_right geom nr.le
  have quad:=error_del_cociente_de_cuadraturas np sp (NNReal.coe_pos.mpr kp) lp bp masa
    (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
  rw [←suma_sin_filtro_como_cociente p np z] at quad
  exact (abs_sub_le _ (sumaSinFiltro h p z/(n:ℝ)) _).trans ((add_le_add normed quad).trans_eq (by ring))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.malla_al_continuo_en_la_misma_densidad
