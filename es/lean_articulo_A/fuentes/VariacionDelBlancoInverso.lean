import BlancoDiscretoDelConteoInverso
import DescarteYProductoBajoLaMasaReal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
private theorem factor_oblicuo (y a : ℝ) (yp : 0≤y) (y1 : y≤1) (ap : 0≤a) (a1 : a≤1) :
    0≤y*(1-a*y) ∧ y*(1-a*y)≤1 ∧ |y*(1-a*y)-(1-a)|≤1-y := by
  have ay:=mul_le_mul a1 y1 yp zero_le_one
  have small:=mul_nonneg ap yp
  have range : |a*(1+y)-1|≤1 := abs_le.mpr ⟨by nlinarith only [ap,small],by nlinarith only [ay,a1]⟩
  have ident : y*(1-a*y)-(1-a)=(1-y)*(a*(1+y)-1) := by ring
  refine ⟨mul_nonneg yp (by linarith), (mul_le_mul y1 (sub_le_self _ small) (by linarith) zero_le_one).trans_eq (one_mul _),?_⟩
  rw [ident,abs_mul,abs_of_nonneg (sub_nonneg.mpr y1)]
  simpa using mul_le_mul_of_nonneg_left range (sub_nonneg.mpr y1)

theorem variacion_del_blanco_inverso {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margin : 2*(C:ℝ)≤κ*n) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ e,|w e|≤W) (y : ℝ≥0) (hy : y≤1) :
    |blancoInverso h p w y-blancoInverso h p w 1|≤2*(1-(y:ℝ))*W*(n:ℝ)^2 := by
  let π:=fun e : Cell n => (probDeLaCasilla h p e:ℝ)
  let a:=fun (u : Mark n) (j : Fin 4) => (probLinea n h p (lineLabel (corners u).2 j):ℝ)
  have unit (u : Mark n) (j : Fin 4) (jj : 2≤j.val) : a u j ≤ 1 := by
    let v : Indice n:=⟨lines (corners u).2 j,on_board (corners u).2 j⟩
    have q:=carga_estricta_en_oblicuas (by omega : 0<n) sp j v jj margin (bal j v)
    change (probLinea n h p (j,v.val):ℝ)≤1
    rw [carga_identificada (by omega : 0<n)]
    exact q.trans (sub_le_self _ (by positivity))
  let D:=fun (z : ℝ) (u : Mark n) (j : Fin 4) => z*(1-a u j*z)
  let weight:=fun u : Mark n => w (corners u).1*(π u.1*π u.2)
  have form (z : ℝ≥0) : blancoInverso h p w z=∑ u∈paresCompatibles n,weight u*(D z u 2*D z u 3) := by
    unfold blancoInverso; apply Finset.sum_congr rfl
    intro u _; dsimp [weight,π,D,a]; ring
  have yp : 0≤(y:ℝ) := y.property
  have y1 : (y:ℝ)≤1 := hy
  have err (u : Mark n) (j : Fin 4) (jj : 2≤j.val) :=
    factor_oblicuo (y:ℝ) (a u j) yp y1 (NNReal.coe_nonneg _) (unit u j jj)
  let cost:=2*(1-(y:ℝ))*W
  have pos : 0≤cost := mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr y1)) wp
  have bound (u : Mark n) :
      |weight u*(D y u 2*D y u 3)-weight u*(D (1:ℝ≥0) u 2*D (1:ℝ≥0) u 3)| ≤ cost*(π u.1*π u.2) := by
    obtain ⟨p₂,b₂,d₂⟩:=err u 2 (by decide)
    obtain ⟨p₃,b₃,d₃⟩:=err u 3 (by decide)
    have z : |1-a u 2|≤1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (unit u 2 (by decide)))]; exact sub_le_self _ (NNReal.coe_nonneg _)
    have id : D y u 2*D y u 3-D 1 u 2*D 1 u 3=
        (D y u 2-D 1 u 2)*D y u 3 + D 1 u 2*(D y u 3-D 1 u 3) := by ring
    have d : |D y u 2*D y u 3-D 1 u 2*D 1 u 3|≤2*(1-(y:ℝ)) := by
      rw [id]; apply (abs_add_le ..).trans
      simp only [D,one_mul,mul_one,abs_mul,abs_of_nonneg p₃]
      linarith only [mul_le_mul d₂ b₃ p₃ (sub_nonneg.mpr y1),
        mul_le_mul z d₃ (abs_nonneg _) zero_le_one]
    rw [←mul_sub,abs_mul]
    have src : 0≤π u.1*π u.2 := by dsimp [π]; positivity
    have wt : |weight u|≤W*(π u.1*π u.2) := by
      dsimp only [weight]; rw [abs_mul,abs_of_nonneg src]; gcongr; exact cap _
    simpa only [cost,mul_assoc,mul_left_comm,mul_comm,NNReal.coe_one] using
      mul_le_mul wt d (abs_nonneg _) (mul_nonneg wp src)
  have mass : ∑ e : Cell n,π e≤(n:ℝ) := by
    rw [show (∑ e : Cell n,π e)=↑(n-h:ℕ) by
      rw [←suma_fisica_del_tablero,masa_exacta_de_fuentes p (by omega : 0<n) sp kp,NNReal.coe_natCast]]
    exact_mod_cast Nat.sub_le n h
  rw [form y,form 1,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun u _ => bound u)).trans _)
  have all:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (paresCompatibles n)) (fun u _ _ => mul_nonneg pos (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) :
      ∀ u : Mark n,u∈Finset.univ → u∉paresCompatibles n → 0≤cost*(π u.1*π u.2))
  apply all.trans
  rw [←Finset.mul_sum,Fintype.sum_prod_type]
  simp_rw [←Finset.mul_sum]; rw [←Finset.sum_mul,pow_two]
  exact mul_le_mul_of_nonneg_left (mul_le_mul mass mass (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _))
    (Nat.cast_nonneg n)) pos
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.variacion_del_blanco_inverso
