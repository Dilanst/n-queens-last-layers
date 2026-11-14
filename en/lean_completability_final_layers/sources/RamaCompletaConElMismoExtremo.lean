import ArticuloAConPerfilFisicoConstruido
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- Common spatial data from the interior up to the endpoint, without a counting hypothesis. -/
theorem existe_rama_normalizada_del_articulo :
    ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ M L : ℝ),
      0<κ ∧ κ≤1 ∧ 1≤M ∧ 0≤L ∧ NormalizacionR15 (p 0) ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)) ∧
      ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L := by
  obtain ⟨P,a,p,regular,_⟩:=articulo_A_con_perfil_fisico_construido
  let b x:=a x*x^2
  have eq x (hx : x∈Ioc (0:ℝ) (1/2)) : EulerFisica (P x) (p x) x.toNNReal (b x):=(regular x hx).1
  have cp x (hx : x∈Ioc (0:ℝ) (1/2)) i := ((regular x hx).2.1 i).continuousOn (s:=rangoF i)
  have ep : 0<techoDEF35:=exp_pos _
  have kp : 0<sueloDiagonalDEF35:=by unfold sueloDiagonalDEF35; positivity
  have k1 : sueloDiagonalDEF35≤1:=by
    unfold sueloDiagonalDEF35
    exact (div_le_one (by positivity)).mpr (by nlinarith only [mul_nonneg (sq_nonneg techoDEF35) (sq_nonneg techoDEF35)])
  have bands x (hx : x∈Ioc (0:ℝ) (1/2)) :=
    bandas_de_orden_cero_sobre_la_rama (eq x hx) (Real.toNNReal_pos.mpr hx.1)
      (by simpa only [Real.coe_toNNReal _ hx.1.le] using hx.2) (cp x hx) (regular x hx).2.2
  have mp:=one_div_pos.mpr (pow_pos ep 2)
  obtain ⟨L,lp,sp⟩:=control_espacial_en_la_rama_abierta kp mp techoDEF35_al_menos_uno
    (by norm_num : (0:ℝ)<1/2) eq (fun x hx=>(bands x hx).1) cp (fun x hx=>(bands x hx).2)
  have low:=lt_min mp kp
  have one:=(min_le_right (1/techoDEF35^2) sueloDiagonalDEF35).trans k1
  obtain ⟨P₀,p₀,b₀,g,ec,sc⟩:=extender_rama_desde_el_interior low one techoDEF35_al_menos_uno lp eq sp
  exact ⟨completarEnCero P P₀,completarEnCero p p₀,completarEnCero b b₀,_,_,L,low,one,
    techoDEF35_al_menos_uno,lp,by simpa [completarEnCero] using g,ec,sc⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existe_rama_normalizada_del_articulo
