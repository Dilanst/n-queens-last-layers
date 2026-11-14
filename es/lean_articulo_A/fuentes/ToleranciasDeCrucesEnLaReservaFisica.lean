import EscalaDelErrorFisicoEnLaReserva
import CambioDeUnaLineaEnLaReserva
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical
open Filter
open scoped Topology

theorem masa_B1_como_marca {n} (v : Cell n→ℝ≥0) (S : Cell n→Prop) :
    masaBajo (fun e=>(v e:ℝ)) S=∑ e,(v e:ℝ)*(mark masas S e).val := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases p : S e <;> simp [pesoCuando,mark,masas,p]

theorem umbrales_de_las_cruces {κ ν : ℝ} (kp : 0<κ) (vn : 0≤ν) :
    ∀ᶠ n : ℕ in atTop,
    let x:=fraccionReserva n
    let q:=n-huecosReserva n
    let η:=κ*x/4
    let d:=Real.toNNReal (100*x)
    let τ:=(n:ℝ)^(-exponenteReserva)
    (d:ℝ)=100*x ∧ (d:ℝ)≤τ^4/8 ∧ (3/4:ℝ≥0)*d≤1 ∧
    ((9*huecosReserva n+2:ℕ):ℝ)≤(((3/4:ℝ≥0)*d):ℝ)*q/3 ∧
    8*errorFisicoReserva κ ν n/η≤(d:ℝ)/16 := by
  have small:=(error_fisico_incluso_en_dos_fracciones kp vn).eventually_lt_const
    (show (0:ℝ)<κ/8 by positivity)
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1,
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const (by norm_num : (0:ℝ)<1/100),small] with n cut hn sx tol
  intro x q η d τ
  have np : 0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have xp : 0<x:=div_pos (by exact_mod_cast cut.1) np
  have de : (d:ℝ)=100*x:=Real.coe_toNNReal _ (by positivity)
  have tau : (1:ℝ)/(n:ℝ)^(4*exponenteReserva)=τ^4:=by
    dsimp [τ]
    rw [←Real.rpow_mul_natCast np.le,show -exponenteReserva*(4:ℕ)=-(4*exponenteReserva) by norm_num; ring,
      Real.rpow_neg np.le,one_div]
  have upper : x≤τ^4/8000:=by
    rw [←tau]
    exact (cut.2.2.2).trans_eq (by ring)
  have xt : x*(n:ℝ)=(huecosReserva n:ℝ):=by dsimp [x,fraccionReserva]; field_simp
  have qeq : (q:ℝ)=(n:ℝ)-(huecosReserva n:ℝ):=Nat.cast_sub cut.2.1
  have half : (n:ℝ)/2≤q:=by
    have z:=mul_le_mul_of_nonneg_right (by linarith only [sx] : x≤1/2) np.le
    linarith only [xt,z,qeq]
  have hmin : (1:ℝ)≤huecosReserva n:=by exact_mod_cast cut.1
  have hp : 0<η:=by dsimp [η]; positivity
  have s:= (div_lt_iff₀ (pow_pos xp 2)).mp tol
  refine ⟨de,?_,?_,?_,?_⟩
  · rw [de]; linarith only [upper,pow_nonneg (Real.rpow_nonneg np.le (-exponenteReserva)) 4]
  · apply NNReal.coe_le_coe.mp
    push_cast
    rw [de]
    change (3/4:ℝ)*(100*x)≤1
    linarith only [sx]
  · push_cast
    rw [de]
    have z:=mul_le_mul_of_nonneg_left half xp.le
    change (9:ℝ)*↑(huecosReserva n)+2≤(3/4)*(100*x)*q/3
    linarith only [z,xt,hmin]
  · rw [de]
    apply (div_le_iff₀ hp).mpr
    change errorFisicoReserva κ ν n<κ/8*x^2 at s
    dsimp [η]
    nlinarith only [s,mul_nonneg kp.le (sq_nonneg x)]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.umbrales_de_las_cruces
