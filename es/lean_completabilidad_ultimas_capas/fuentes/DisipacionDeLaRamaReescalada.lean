import TrabajoConjuntoDeDosTableros
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Filter Perfil
private theorem integral_constante_de_linea (i : Fin 4) (Z : ℝ) :
    (∫ _ : ℝ,Z ∂marginalRef i)=(if i.val<2 then 1 else 2)*Z := by
  fin_cases i <;> norm_num [marginalRef,integral_const,Real.volume_Ioc,ENNReal.toReal_ofReal,smul_eq_mul]

theorem trabajo_de_la_rama_acotado {P Q p q x y b c κ M L}
    (ex : EulerFisica P p x b) (ey : EulerFisica Q q y c)
    (sp : ControlEspacial p κ M L) (sq : ControlEspacial q κ M L) (kp : 0<κ) (lp : 0≤L) :
    trabajoRelativo P Q≤|(y:ℝ)-x| *(|Real.log b-Real.log c|+2*M*(2*(|Real.log κ|+|Real.log M|))) := by
  let v:=fun i s=>logR15 p i s-logR15 q i s
  let D:=2*(|Real.log κ|+|Real.log M|)
  have nonD : 0≤D := by dsimp [D]; positivity
  have nonM : 0≤M := kp.le.trans ((banda_de_campo sp 0 0).1.trans (banda_de_campo sp 0 0).2)
  have bv (i : Fin 4) (s : ℝ) : |v i s|≤D := (abs_sub _ _).trans
    (by dsimp [D]; linarith only [banda_del_logaritmo sp kp i s,banda_del_logaritmo sq kp i s])
  have mv (i : Fin 4) : Measurable (v i) := ((continuo_del_logaritmo sp kp lp i).sub
    (continuo_del_logaritmo sq kp lp i)).measurable
  have eq : ∀ᵐ z ∂cuadrado,Real.log (P.ν z)-Real.log (Q.ν z)=
      (Real.log b-Real.log c)+∑ i,v i (coord i z) := by
    filter_upwards [log_de_la_densidad_normalizada ex sp kp,log_de_la_densidad_normalizada ey sq kp] with z hx hy
    simp only [v,Finset.sum_sub_distrib,hx,hy]; ring
  rw [descomposicion_del_trabajo P Q _ v mv (fun i=>⟨D,bv i⟩) eq,ex.masa,ey.masa]
  let term:=fun i=> ∫ s,((P.m i s:ℝ)-Q.m i s)*v i s ∂marginalRef i
  have hb (i : Fin 4) : term i≤(if i.val<2 then 1 else 2)*(|coefLinea y i-coefLinea x i| *M*D) := by
    rw [←integral_constante_de_linea]
    have it:=(P.m_integrable i |>.sub (Q.m_integrable i)).bdd_mul (mv i).aestronglyMeasurable ⟨D,bv i⟩
    apply integral_mono_ae (by simpa only [mul_comm,Pi.sub_apply] using it) (integrable_const _)
    filter_upwards [masa_de_linea_normalizada ex i,masa_de_linea_normalizada ey i] with t hx hy
    rw [hx,hy]
    apply termino_de_linea_entre_densidades _ (kp.trans_le (banda_de_campo sp i t).1)
      (kp.trans_le (banda_de_campo sq i t).1) (banda_de_campo sq i t).2 (bv i t)
    unfold coefLinea; split_ifs <;> positivity
  have su:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hb i)
  norm_num [Fin.sum_univ_four,coefLinea,show ¬(3:Fin 4).val<2 by decide] at su
  change (1-(x:ℝ)-(1-(y:ℝ)))*(Real.log b-Real.log c)+∑ i,term i≤_
  have g : (1-(x:ℝ)-(1-(y:ℝ)))*(Real.log b-Real.log c)≤|(y:ℝ)-x| *|Real.log b-Real.log c| := by
    rw [show 1-(x:ℝ)-(1-(y:ℝ))=(y:ℝ)-x by ring,←abs_mul]; exact le_abs_self _
  rw [Fin.sum_univ_four]
  dsimp [D] at su
  nlinarith only [g,su]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.trabajo_de_la_rama_acotado
