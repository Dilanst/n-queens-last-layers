import ReindexacionDeLasDosEsquinas
import DescarteDeParejasDelBlancoInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Trayectoria.Adjunto
def vacanciasDeLaEsquina {n} (h : ℕ) (p : FactoresContinuos) (e : Cell n) : ℝ :=
  (1-(cargaDeDestino h p e e 0:ℝ))*(1-(cargaDeDestino h p e e 1:ℝ))

theorem vacancias_inversas_en_su_centro {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margin : 2*(C:ℝ)≤κ*n) (e : Cell n) :
    |vacanciasDeLaEsquina h p e|≤1 ∧
    |vacanciasDeLaEsquina h p e-psiEnElCentro p e|≤(1+(m:ℝ))*((C:ℝ)/n) := by
  let a:=fun j : Fin 4 => 1-(cargaDeDestino h p e e j:ℝ)
  let b:=holgurasFisicas p e e
  have est (j : Fin 4) : |a j-b j|≤(C:ℝ)/n := by
    simpa only [a,b,NNReal.coe_sub ((cargas_para_un_cruce hn sp kp bal margin e).1 e j),NNReal.coe_one]
      using diferencia_en_el_destino hn sp kp bal margin e e j
  have pos (j : Fin 4) : 0≤a j := sub_nonneg.mpr (NNReal.coe_le_coe.mpr ((cargas_para_un_cruce hn sp kp bal margin e).1 e j))
  have bounded (j : Fin 4) : |a j|≤1 := by rw [abs_of_nonneg (pos j)]; exact sub_le_self _ (NNReal.coe_nonneg _)
  have b0 : |b 0|≤m := rango_de_holguras sp (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
    (medio_admisible e.1.isLt) (medio_admisible e.2.isLt) 0
  change |a 0*a 1|≤1 ∧ |a 0*a 1-b 0*b 1|≤_
  constructor
  · rw [abs_mul]; simpa using mul_le_mul (bounded 0) (bounded 1) (abs_nonneg _) zero_le_one
  · rw [show a 0*a 1-b 0*b 1=(a 0-b 0)*a 1+b 0*(a 1-b 1) by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    have u:=mul_le_mul (est 0) (bounded 1) (abs_nonneg _) (div_nonneg C.property (Nat.cast_nonneg n))
    have v:=mul_le_mul b0 (est 1) (abs_nonneg _) m.property
    linarith only [u,v]

theorem eliminar_filtro_y_reemplazar_vacancias {n h} {p : FactoresContinuos} {κ m C : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (bal : BalanceMalla n h p C)
    (margin : 2*(C:ℝ)≤κ*n) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W) :
    |blancoInverso h p w 1-sumaInversaDeLosCentros h p w|≤
    (4*W*((m:ℝ)^4/κ^4)^2 + W*(1+(m:ℝ))*C)*(n:ℝ) := by
  let π:=fun e : Cell n => (probDeLaCasilla h p e:ℝ)
  let M:ℝ:=(m:ℝ)^4/κ^4
  let g:=fun u : Mark n => w (corners u).1*(π u.1*π u.2)*vacanciasDeLaEsquina h p (corners u).2
  let v:=fun u : Mark n => w (corners u).1*(π u.1*π u.2)*psiEnElCentro p (corners u).2
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have pp (e : Cell n) : 0≤π e := NNReal.coe_nonneg _
  have mp : 0≤M := by dsimp [M]; positivity
  have lim (e : Cell n) : π e≤M/n := (le_div_iff₀ np).mpr (by
    simpa only [M,π,mul_comm,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_pow] using
      NNReal.coe_le_coe.mpr ((cargas_para_un_cruce hn sp kp bal margin e).2 e))
  have wt (u : Mark n) : |w (corners u).1*(π u.1*π u.2)|≤W*(π u.1*π u.2) := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (pp _) (pp _))]; gcongr; exact cap _
  have excluded:=error_de_pares_excluidos g (W*(M/n)^2) (by positivity) (fun u => by
    dsimp only [g]; rw [abs_mul]
    have p:=mul_le_mul (lim u.1) (lim u.2) (pp _) (div_nonneg mp np.le)
    have b:=mul_le_mul ((wt u).trans (mul_le_mul_of_nonneg_left p wp))
      (vacancias_inversas_en_su_centro hn sp kp bal margin (corners u).2).1 (abs_nonneg _)
      (mul_nonneg wp (mul_nonneg (div_nonneg mp np.le) (div_nonneg mp np.le)))
    simpa only [mul_one,pow_two] using b)
  have sum : (∑ u : Mark n,π u.1*π u.2) ≤ (n:ℝ)^2 := by
    rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum]; rw [←Finset.sum_mul,pow_two]
    have mass : ∑ e : Cell n,π e≤(n:ℝ) := by
      rw [←suma_fisica_del_tablero,masa_exacta_de_fuentes p (by omega : 0<n) sp kp,NNReal.coe_natCast]
      exact_mod_cast Nat.sub_le n h
    exact mul_le_mul mass mass (Finset.sum_nonneg (fun e _ => pp e)) np.le
  let D:=(1+(m:ℝ))*((C:ℝ)/n)
  have dp : 0≤D := by dsimp [D]; positivity
  have diff : |(∑ u,g u)-(∑ u,v u)|≤W*D*n^2 := by
    rw [←Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs ..).trans
    calc _ ≤ ∑ u : Mark n,(W*D)*(π u.1*π u.2) := by
              apply Finset.sum_le_sum; intro u _
              dsimp only [g,v]; rw [←mul_sub,abs_mul]
              simpa only [mul_assoc,mul_comm,mul_left_comm,D] using mul_le_mul (wt u)
                (vacancias_inversas_en_su_centro hn sp kp bal margin (corners u).2).2 (abs_nonneg _)
                (mul_nonneg wp (mul_nonneg (pp _) (pp _)))
         _ ≤ _ := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left sum (mul_nonneg wp dp)
  have original : blancoInverso h p w 1=∑ u∈paresCompatibles n,g u := by
    unfold blancoInverso; apply Finset.sum_congr rfl
    intro u _
    change w _*((π u.1)*(1:ℝ≥0))*((π u.2)*(1:ℝ≥0))*(1-_*((1:ℝ≥0):ℝ))*(1-_*((1:ℝ≥0):ℝ))=_
    simp only [NNReal.coe_one,mul_one]; dsimp [g,vacanciasDeLaEsquina,cargaDeDestino,lineLabel,side,key,dest,corners]; ring
  have full : sumaInversaDeLosCentros h p w=∑ u,v u := by
    unfold sumaInversaDeLosCentros; apply Finset.sum_congr rfl; intro u _; dsimp [v,π]; ring
  rw [original,full]
  apply (abs_sub_le _ (∑ u,g u) _).trans
  rw [abs_sub_comm] at excluded
  apply (add_le_add excluded diff).trans_eq
  dsimp [D,M]; field_simp; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.vacancias_inversas_en_su_centro
#print axioms ArticuloA.Historias.eliminar_filtro_y_reemplazar_vacancias
