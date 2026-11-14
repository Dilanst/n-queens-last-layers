import PerdidaDeLasCuatroCoordenadas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Corte
noncomputable section

private theorem potenciaFisica (r : ℝ≥0) (j : ℕ) : Control.power masas r j=r^j := by
  induction j with
  | zero => rfl
  | succ j ih => change r*Control.power masas r j=_; rw [ih,pow_succ,mul_comm]

theorem resto_del_blanco {n : ℕ} {N z u E B H ζ V Y loss : ℝ≥0} (j : ℕ)
    (hn : 0<n) (nN : (n:ℝ≥0)≤N) (zeta : 0<ζ) (lo : ζ≤z) (top : z≤1) (paso : u+N⁻¹=z)
    (grado : j≤4) (pares : pairsN j≤6) (ini : V≤n*H)
    (cerca : within masas Y (V*z^j) E)
    (localEst : within masas loss (Y*((j:ℝ≥0)*(N*z)⁻¹)) (B*(E+1)/n)) :
    |(loss:ℝ)+↑(V*u^j)-↑(V*z^j)| ≤ ((B+4/ζ+6*H/ζ^2)*(E+1)/n).val := by
  have np : 0<(n:ℝ≥0) := by exact_mod_cast hn
  have Np:=np.trans_le nN
  have zp:=zeta.trans_le lo
  let a:ℝ≥0:=(N*z)⁻¹
  let r:=u/z
  have splitClock : r+a=1 := by
    change u/z+(N*z)⁻¹=1
    rw [mul_inv,←div_eq_mul_inv N⁻¹ z,←add_div,paso,div_self zp.ne']
  have step := Region.target_decrement (s:=masas) r a Y (V*z^j) loss E (B*(E+1)/n) j splitClock
    (by rw [times_m,ns_real]; change within masas loss (((j:ℝ≥0)*a)*Y) _; rwa [mul_comm _ Y]) cerca
  have survival:=survive masas r a splitClock j
  rw [potenciaFisica] at survival
  change r^j+a*geom masas r j=1 at survival
  have zr : z*r=u := by dsimp [r]; field_simp
  have identity : (V*u^j)+(V*z^j)*(a*geom masas r j)=V*z^j := by
    rw [←zr,mul_pow]; calc
      _ = (V*z^j)*(r^j+a*geom masas r j) := by ring
      _ = _ := by rw [survival,mul_one]
  have acap : a≤((n:ℝ≥0)*ζ)⁻¹ := inv_anti₀ (mul_pos np zeta) (mul_le_mul' nN lo)
  have vcap : V*z^j≤(n:ℝ≥0)*H := (mul_le_mul_left' (pow_le_one₀ (zero_le _) top) _).trans (by simpa using ini)
  have j4 : (j:ℝ≥0)≤4 := by exact_mod_cast grado
  have j6 : (pairsN j:ℝ≥0)≤6 := by exact_mod_cast pares
  let K:=B*(E+1)/n+(((j:ℝ≥0)*a)*E+(V*z^j)*((a*a)*(pairsN j:ℝ≥0)))
  have scale : K≤(B+4/ζ+6*H/ζ^2)*(E+1)/n := by
    calc K ≤ B*(E+1)/n+((4*((n:ℝ≥0)*ζ)⁻¹)*E+((n:ℝ≥0)*H)*(((((n:ℝ≥0)*ζ)⁻¹)*((n:ℝ≥0)*ζ)⁻¹)*6)) :=
            add_le_add_left (add_le_add (mul_le_mul_right' (mul_le_mul' j4 acap) E)
              (mul_le_mul' vcap (mul_le_mul' (mul_le_mul' acap acap) j6))) _
         _ ≤ _ := by
            apply (le_iff_exists_nonneg_add).mpr
            refine ⟨(4/ζ+6*H*E/ζ^2)/n,zero_le _,?_⟩
            field_simp; ring
  simp only [times_m,ns_real] at step
  have e1 : loss≤(V*z^j)*(a*geom masas r j)+K := step.1
  have e2 : (V*z^j)*(a*geom masas r j)≤loss+K := step.2
  have ir:=(congrArg NNReal.toReal identity)
  have b1:=NNReal.coe_le_coe.mpr e1
  have b2:=NNReal.coe_le_coe.mpr e2
  have sc:=NNReal.coe_le_coe.mpr scale
  simp only [NNReal.coe_add] at ir b1 b2
  have scalar (x u z f k b : ℝ) (id : u+f=z) (le : x≤f+k) (ge : f≤x+k) (kb : k≤b) : |x+u-z|≤b := by
    apply abs_le.mpr; constructor <;> linarith
  exact scalar _ _ _ _ _ _ ir b1 b2 sc
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.resto_del_blanco
