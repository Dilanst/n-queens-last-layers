import CandidatosEnLaLeyOriginalE2
import ToleranciaLinealDelAbsorbedor
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

theorem cuenta_directa_hasta_el_corte (κ m ζ C γ : ℝ≥0) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (gp : 0<γ) :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,∀ n≥N,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
    ControlEspacial p κ m L → BalanceMalla n h p C → ∀ T≤2*n-1,ζ≤fraccionAntes n T → ∀ z : Cell n,
    let w:=coloresDelPerfil n h p
    let ini:=blancoDeLaRaiz ((T:ℝ≥0)/(↑(2*n-1):ℝ≥0)) z (cargaDeDestino h p z) (probDeLaCasilla h p)
    (avg masas (rutas (kernel masas w (·⁻¹)) 0 T (initial n h)) (mark masas (fun l => (γ:ℝ)*n≤
      |(physicalCount (estadoEn (initial n h) l T).physical z:ℝ)-(ini:ℝ)|))).val ≤3*Real.exp (-(c*n)) := by
  let D:=constanteDirecta m κ ζ C
  let B:=saltoDirecto ζ (m^4/κ^4)
  have pf:=piso_positivo kp zp
  obtain ⟨ε,ep,adm,N₁,room⟩:=tolerancia_para_la_raiz D _ γ pf gp
  obtain ⟨c₁,c₁p,N₂,reg⟩:=regularidad_hasta_el_corte κ m ζ C ε kp m1 zp ep adm
  have bb : 0<(B:ℝ)+1 := by exact add_pos_of_nonneg_of_pos B.property zero_lt_one
  obtain ⟨θ,c₂,tp,cp,small,ex⟩:=exponente_hasta_el_corte ((B:ℝ)+1) ((γ:ℝ)/2) bb (by positivity)
  obtain ⟨N₃,big⟩:=exists_nat_gt ((2*C/piso κ ζ+2*C/κ:ℝ≥0):ℝ)
  refine ⟨min c₁ c₂,lt_min c₁p cp,max 2 (max N₁ (max N₂ N₃)),?_⟩
  intro n hn h hh p L sp bal T tN fl z w ini
  have n2 : 2≤n := by omega
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
  have t2 : T≤2*n := by omega
  have size : 2*C/piso κ ζ+2*C/κ≤(n:ℝ≥0) := NNReal.coe_le_coe.mp (big.le.trans (by exact_mod_cast (by omega : N₃≤n)))
  have hζ := (div_le_iff₀ pf).mp (show 2*C/piso κ ζ≤(n:ℝ≥0) from (le_add_of_nonneg_right (zero_le _)).trans size)
  have hκ := (div_le_iff₀ kp).mp (show 2*C/κ≤(n:ℝ≥0) from (le_add_of_nonneg_left (zero_le _)).trans size)
  have mar : 2*(C:ℝ)≤κ*n := by exact_mod_cast (show 2*C≤κ*n by simpa only [mul_comm] using hκ)
  have ho : 2*C/n≤piso κ ζ := (div_le_iff₀ np).mpr (by simpa only [mul_comm] using hζ)
  have he : (ε*n)/n≤piso κ ζ := by rwa [mul_div_cancel_right₀ _ np.ne']
  have θB : θ*(B:ℝ)≤1 := (mul_le_mul_of_nonneg_left (by linarith : (B:ℝ)≤B+1) tp.le).trans small
  have az:=candidatas_sin_condicionar n2 hh sp kp m1 zp tN fl bal mar he ho z θ ((γ:ℝ)/2*n) tp.le θB
  have rg:=reg n (by omega) h hh p L sp bal T tN fl
  have margin:=NNReal.coe_le_coe.mpr (room n (by omega) T t2)
  simp only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_ofNat] at margin
  let ley:=rutas (kernel masas w (·⁻¹)) 0 T (initial n h)
  let dev:=fun l => |(physicalCount (estadoEn (initial n h) l T).physical z:ℝ)-(ini:ℝ)|
  have inc:=misma_masa_en_el_soporte ley (fun l => (γ:ℝ)*n≤dev l)
    (fun l => (γ:ℝ)/2*n+T*((D*(ε*n+1)/n:ℝ≥0):ℝ)≤dev l) (by
      intro i _ _ yes; change (γ:ℝ)*n≤dev i.2 at yes
      simp only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_div] at *; linarith only [yes,margin])
  have xx : T*(θ*(B:ℝ))^2-θ*((γ:ℝ)/2*n)≤ -(c₂*n) := by
    apply le_trans _ (ex n T t2); gcongr; linarith
  have w₁:=Real.exp_le_exp.mpr (show -(c₁*n)≤ -(min c₁ c₂*n) by gcongr; exact min_le_left _ _)
  have w₂:=Real.exp_le_exp.mpr (show -(c₂*n)≤ -(min c₁ c₂*n) by gcongr; exact min_le_right _ _)
  have both:=(NNReal.coe_le_coe.mpr inc).trans az
  have mid:=Real.exp_le_exp.mpr xx
  change _≤_+2*Real.exp ((T:ℝ)*(θ*(B:ℝ))^2-θ*((γ:ℝ)/2*n)) at both
  apply both.trans
  have cmp:=add_le_add (rg.trans w₁) (mul_le_mul_of_nonneg_left (mid.trans w₂) (by norm_num : (0:ℝ)≤2))
  exact cmp.trans_eq (by ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuenta_directa_hasta_el_corte
