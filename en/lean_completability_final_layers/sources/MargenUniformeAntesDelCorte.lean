import PesosYCuotasAntesDelCorte
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def piso (κ ζ : ℝ≥0) := min (ζ/8) (min (κ^4*ζ^4/4) (ζ^4/4))
def techo (m κ ζ : ℝ≥0) := 2+m^4+m+(m^4/κ^4)/piso κ ζ+m/piso κ ζ

theorem piso_positivo {κ ζ : ℝ≥0} (kp : 0<κ) (zp : 0<ζ) : 0<piso κ ζ := by
  unfold piso; exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

theorem margenes_del_reloj {n h : ℕ} {p : FactoresContinuos} {κ m ζ z : ℝ≥0} {L : ℝ} (hn : 2≤n)
    (sp : ControlEspacial p (κ:ℝ≥0) (m:ℝ≥0) L) (hz : (ζ:ℝ≥0)≤z) (z1 : z≤1)
    (err off : ℝ≥0) (he : err≤piso κ ζ) (ho : off≤piso κ ζ) :
    piso κ ζ≤relojIni n*z ∧ piso κ ζ≤relojIni n*z^4 ∧ relojIni n*z≤2 ∧
    piso κ ζ+err≤totalIni n h p*z^4 ∧ piso κ ζ+(err+off)≤cuotaV n h*z := by
  obtain ⟨rc,r2,_,v2,_⟩:=cotas_reloj_y_cuotas hn h
  have small : piso κ ζ≤ζ/8 := min_le_left .. 
  have smallW : piso κ ζ≤κ^4*ζ^4/4 := (min_le_right ..).trans (min_le_left ..)
  have smallZ : piso κ ζ≤ζ^4/4 := (min_le_right ..).trans (min_le_right ..)
  have clock : ζ≤relojIni n*z := by simpa only [one_mul] using mul_le_mul' rc hz
  have four : ζ^4≤relojIni n*z^4 := by simpa only [one_mul] using mul_le_mul' rc (pow_le_pow_left' hz 4)
  have low := suelo_total_fisico (h:=h) (by omega : 0<n) sp
  have W:=mul_le_mul' low (pow_le_pow_left' hz 4)
  have U:=mul_le_mul' v2 hz
  refine ⟨le_trans (by exact small.trans (div_le_self (zero_le _) (by norm_num))) clock,
    le_trans (by exact smallZ.trans (div_le_self (zero_le _) (by norm_num))) four,
    by simpa only [mul_one] using mul_le_mul' r2 z1,?_,?_⟩
  · apply le_trans _ W
    exact_mod_cast (show (piso κ ζ:ℝ)+(err:ℝ)≤(κ:ℝ)^4*(ζ:ℝ)^4 by
      have r : (piso κ ζ:ℝ)≤(κ:ℝ)^4*(ζ:ℝ)^4/4 := by exact_mod_cast smallW
      have b : (err:ℝ)≤(piso κ ζ:ℝ) := he
      linarith [mul_nonneg (show 0≤(κ:ℝ)^4 by positivity) (show 0≤(ζ:ℝ)^4 by positivity)])
  · apply le_trans _ U
    exact_mod_cast (show (piso κ ζ:ℝ)+((err:ℝ)+(off:ℝ))≤(1/2:ℝ)*(ζ:ℝ) by
      have r : (piso κ ζ:ℝ)≤(ζ:ℝ)/8 := by exact_mod_cast small
      have b : (err:ℝ)≤(piso κ ζ:ℝ) := he
      have c : (off:ℝ)≤(piso κ ζ:ℝ) := ho
      calc
        _ ≤ 3*((ζ:ℝ)/8) := by linarith only [r,b,c]
        _ ≤ _ := by nlinarith only [show (0:ℝ)≤ζ from ζ.property])

theorem techos_comunes (m κ ζ : ℝ≥0) : 2≤techo m κ ζ ∧ m^4≤techo m κ ζ ∧ m≤techo m κ ζ ∧
    (m^4/κ^4)/piso κ ζ≤techo m κ ζ ∧ m/piso κ ζ≤techo m κ ζ := by
  unfold techo
  generalize m^4=u
  generalize u/κ^4/piso κ ζ=v
  generalize m/piso κ ζ=w
  exact_mod_cast (show (2:ℝ)≤2+(u:ℝ)+m+v+w ∧ (u:ℝ)≤2+u+m+v+w ∧ (m:ℝ)≤2+u+m+v+w ∧
    (v:ℝ)≤2+u+m+v+w ∧ (w:ℝ)≤2+u+m+v+w by
    refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith only [show (0:ℝ)≤m from m.property,show (0:ℝ)≤v from v.property,
      show (0:ℝ)≤w from w.property,show (0:ℝ)≤u from u.property])

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.margenes_del_reloj
