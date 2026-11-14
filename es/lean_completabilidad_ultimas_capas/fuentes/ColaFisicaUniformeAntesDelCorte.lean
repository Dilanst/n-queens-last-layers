import ConcentracionInversaEnLaLeyOriginal
import ToleranciaDelConteoInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
/-- Constants are chosen before n, its level, its horizon, and the signed test. -/
theorem cola_uniforme_del_inverso_original (κ m ζ C ε : ℝ≥0) (W : ℝ) (wp : 0≤W)
    (kp : 0<κ) (m1 : 1≤m) (zp : 0<ζ) (ep : 0<ε) :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,∀ n≥N,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
    ControlEspacial p κ m L → BalanceMalla n h p C → ∀ T≤2*n-1,ζ≤fraccionAntes n T →
    ∀ w : Cell n→ℝ,(∀ z,|w z|≤W) →
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    let target:=blancoInverso h p w (horizonteInverso n T 0)
    (avg masas (rutas S 0 T (initial n h)) (mark masas (fun l =>
      (ε:ℝ)*(n:ℝ)^2≤|inversasDelTablero (estadoEn (initial n h) l T).physical w-target|))).val
        ≤3*Real.exp (-(c*(n:ℝ))) := by
  obtain ⟨e,pe,ad,s,sp,sm,tilt,N₁,room⟩:=parametros_del_conteo_inverso κ m ζ C ε W wp kp zp ep
  obtain ⟨c,cp,N₂,exit⟩:=regularidad_hasta_el_corte κ m ζ C e kp m1 zp pe ad
  obtain ⟨N₃,large⟩:=exists_nat_gt ((2*C/piso κ ζ:ℝ≥0):ℝ)
  have ep' : 0<(ε:ℝ) := ep
  let r:=min c (s*ε/4)
  have rp : 0<r := lt_min cp (by positivity)
  refine ⟨r,rp,max 2 (max N₁ (max N₂ N₃)),?_⟩
  intro n hn h hh p L space bal T tN fl w cap S target
  have nn : 2≤n := by omega
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
  have he : e*n/n≤piso κ ζ := by rw [mul_div_cancel_right₀ _ np.ne']; exact ad
  have enough : 2*C/piso κ ζ≤(n:ℝ≥0) := NNReal.coe_le_coe.mp
    (large.le.trans (by exact_mod_cast (by omega : N₃≤n)))
  have ho : 2*C/n≤piso κ ζ := (div_le_iff₀ np).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ (piso_positivo kp zp)).mp enough)
  have a:=concentracion_inversa_en_la_ley_original nn hh space kp m1 zp tN fl bal he ho w wp cap ε s ep' sp sm tilt
    (room n (by omega))
  have b:=exit n (by omega) h hh p L space bal T tN fl
  have e1 : Real.exp (-(c*(n:ℝ)))≤Real.exp (-(r*(n:ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left ..) (Nat.cast_nonneg n)))
  have e2 : Real.exp (-(s*(ε:ℝ)/4)*(n:ℝ))≤Real.exp (-(r*(n:ℝ))) := by
    rw [neg_mul]; apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right ..) (Nat.cast_nonneg n))
  exact a.trans (by linarith only [b,e1,e2])
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_uniforme_del_inverso_original
