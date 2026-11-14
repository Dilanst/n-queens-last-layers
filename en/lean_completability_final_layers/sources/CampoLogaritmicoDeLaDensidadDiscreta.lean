import SumaDeDosEtiquetadosDeLasMismasFibras
import BalanceUniformeParaElNumeroDeHuecosVariable
namespace ArticuloA.Historias
open Perfil Repair Trayectoria Trayectoria.E2 Real
open scoped BigOperators NNReal
noncomputable section
open Classical

theorem log_del_peso_de_casilla {n h q : ℕ} {p κ M L} (hn : 0<n) (hq : 0<q)
    (x : ℝ≥0) (eqx : x=fraccionHuecos n h) (xp : 0<(x:ℝ)) (kp : 0<κ)
    (sp : ControlEspacial p κ M L) (e : Cell n) :
    log (cargaCelda n q p e) = log (q:ℝ)-log ((x:ℝ)^2*Wfisico n p)+
      ∑ i,log (holguraInicial n h p i (lineaDeCuadratura e i)) := by
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have qp : 0<(q:ℝ):=by exact_mod_cast hq
  have pp : 0<pesoFisico n p e:=(pow_pos kp 4).trans_le ((limites_del_producto sp kp.le _ _
    (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)).1)
  have wp : 0<Wfisico n p:=(mul_pos (pow_pos kp _) (pow_pos np 2)).trans_le (masa_inferior sp kp.le)
  let U (i : Fin 4):=holguraInicial n h p i (lineaDeCuadratura e i)
  have prod : (∏ i,U i)=(x:ℝ)^2*pesoFisico n p e := by
    dsimp only [U]
    simp_rw [virtual_de_la_malla,←eqx]
    exact muestra_real x p e
  have nonz : (∏ i,U i)≠0:=by rw [prod]; positivity
  have logs:=Real.log_prod Finset.univ U ((Finset.prod_ne_zero_iff).mp nonz)
  rw [prod,log_mul (pow_ne_zero 2 xp.ne') pp.ne'] at logs
  change log ((q:ℝ)*pesoFisico n p e/Wfisico n p)=_+∑ i,log (U i)
  rw [log_div (mul_ne_zero qp.ne' pp.ne') wp.ne',log_mul qp.ne' pp.ne',
    log_mul (pow_ne_zero 2 xp.ne') wp.ne',←logs]
  ring

theorem suma_del_campo_por_fibras {n q : ℕ} (p : FactoresContinuos) (i : Fin 4)
    (g : Indice n→ℝ) :
    (∑ e : Cell n,cargaCelda n q p e*g (lineaDeCuadratura e i))=
      ∑ j : Indice n,cargaLinea n q p i j*g j := by
  have one (j : Indice n) :
      cargaLinea n q p i j*g j =
      ∑ e : Cell n,if lineaDeCuadratura e i=j then cargaCelda n q p e*g j else 0 := by
    unfold cargaLinea gradoInicial
    rw [Finset.mul_sum,Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : lineaDeCuadratura e i=j
    · have v : lines e i=j.val:=congrArg Fin.val h
      simp [h,v,cargaCelda]
    · have v : lines e i≠j.val:=fun he=>h (Fin.ext he)
      simp [h,v]
  simp_rw [one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

theorem entropia_de_celdas_en_el_campo {n h q : ℕ} {p κ M L} (hn : 0<n) (hq : 0<q)
    (x : ℝ≥0) (eqx : x=fraccionHuecos n h) (xp : 0<(x:ℝ)) (kp : 0<κ)
    (sp : ControlEspacial p κ M L) :
    entropiaCeldas (cargaCelda n q p)=(q:ℝ)*(log ((x:ℝ)^2*Wfisico n p)-log q)-
      ∑ i,∑ j : Indice n,cargaLinea n q p i j*log (holguraInicial n h p i j) := by
  let A:=log ((x:ℝ)^2*Wfisico n p)-log q
  let w:=cargaCelda n q p
  let U:=holguraInicial n h p
  have point (e : Cell n) : aporteCelda (w e)=w e*A-∑ i,w e*log (U i (lineaDeCuadratura e i)) := by
    dsimp only [aporteCelda,w,U,A]
    rw [log_del_peso_de_casilla hn hq x eqx xp kp sp e,←Finset.mul_sum]
    ring
  change ∑ e,aporteCelda (w e)=_
  simp_rw [point]
  have dual : (∑ e : Cell n,∑ i,w e*log (U i (lineaDeCuadratura e i)))=
      ∑ i,∑ j : Indice n,cargaLinea n q p i j*log (U i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact suma_del_campo_por_fibras p i (fun j=>log (U i j))
  rw [Finset.sum_sub_distrib,←Finset.sum_mul,(masa_y_signo_de_la_densidad_fisica (q:=q) hn sp kp).1,dual]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_celdas_en_el_campo
