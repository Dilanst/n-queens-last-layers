import ErrorDelPasoInversoPonderado
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

/-- Unnormalized drift error at one physical running state of E2, compared with
the sixteen ideal equations. The same signed coefficients are used in both drifts. -/
theorem deriva_inversa_sumada {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (leg : Legal X.physical) (coh : coherent X) (running : X.failed=false) (W : ℝ) (wp : 0≤W)
    (coef : CuatroMarcas→Mark n→ℝ) (cap : ∀ t,∀ u∈paresCompatibles n,|coef t u|≤W*(escalaDelPatron n t:ℝ)) :
    let A:=region_del_estado hn hh sp kp m1 zp hz z1 bal he ho X reg
    let D : ℝ≥0:=constanteUna (piso κ ζ) (techo m κ ζ) C*(E+1)
    let H : ℝ≥0:=m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)
    |∑ t : CuatroMarcas,∑ u∈paresCompatibles n,coef t u*errorDeDeriva A t u|≤
      W*(192*(D:ℝ)+720*(H:ℝ)) := by
  intro A D H
  let cost:=fun t : CuatroMarcas => costoDeUnPatron A t.1 t.2.1 t.2.2.1 t.2.2.2
  have nn : (n:ℝ≥0)≠0 := by exact_mod_cast (show 0<n by omega).ne'
  have cancel (v : ℝ≥0) : (n:ℝ≥0)*(v/n)≤v := le_of_eq (by field_simp)
  have costs : (∑ t : CuatroMarcas,cost t)≤192*D :=
    presupuesto_de_los_canales A (by omega) leg E C (cancel E) (cancel (2*C)) (cancel C)
  have costs' : ∑ t : CuatroMarcas,(cost t:ℝ)≤192*(D:ℝ) := by exact_mod_cast costs
  have step (t : CuatroMarcas) : |∑ u∈paresCompatibles n,coef t u*errorDeDeriva A t u|≤
      W*((cost t:ℝ)+45*(H:ℝ)) := by
    have one:=cota_del_paso_por_patron A coh running t (coef t) W wp (cap t)
    have overlap:=resto_del_paso_ponderado hn hh sp kp m1 zp hz z1 bal he ho X reg leg
      t.1 t.2.1 t.2.2.1 t.2.2.2
    apply one.trans; apply mul_le_mul_of_nonneg_left _ wp; apply add_le_add_left
    have qty : escalaDelPatron n t*masas.sum (soporteInverso X t) (impactoMultiple X (coloresDelPerfil n h p) t)≤45*H := overlap
    exact_mod_cast qty
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun t _ => step t)).trans
  rw [←Finset.mul_sum,Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ wp
  have cnt : Fintype.card CuatroMarcas=16 := by decide
  simp only [Finset.sum_const,Finset.card_univ,cnt,nsmul_eq_mul,Nat.cast_ofNat]
  linarith only [costs']

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_inversa_sumada
