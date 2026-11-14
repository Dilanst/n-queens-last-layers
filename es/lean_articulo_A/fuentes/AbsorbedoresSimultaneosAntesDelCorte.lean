import UnaLeyParaTodasLasRaicesYTiempos
import ColaExponencialParaLaCuentaDirecta
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

private theorem absorber_raices_y_tiempos (c : ℝ) (cp : 0<c) :
    ∃ N : ℕ,∀ n≥N,∀ T≤2*n, (n:ℝ)^2*(T+1)*(3*Real.exp (-(c*n)))≤Real.exp (-(c/2*n)) := by
  obtain ⟨N,big⟩:=exists_nat_gt (9*24/(c/2)^4)
  refine ⟨max 1 N,?_⟩
  intro n hn T cut
  have n1 : 1≤(n:ℝ) := by exact_mod_cast (by omega : 1≤n)
  have t : (T:ℝ)≤2*n := by exact_mod_cast cut
  have tn : (T:ℝ)+1≤3*n := by linarith
  have room : 9*24/(c/2)^4≤(n:ℝ) := big.le.trans (by exact_mod_cast (by omega : N≤n))
  have large:=(div_le_iff₀ (show 0<(c/2)^4 by positivity)).mp room
  have bound:=mul_le_mul_of_nonneg_right large (show 0≤(n:ℝ)^3 by positivity)
  have exp:=Real.pow_div_factorial_le_exp (c/2*(n:ℝ)) (by positivity) 4
  norm_num [Nat.factorial] at exp
  have pen : 9*(n:ℝ)^3≤Real.exp (c/2*n) := by nlinarith only [bound,exp]
  have poly : (n:ℝ)^2*(T+1)*3≤9*n^3 := by nlinarith only [mul_le_mul_of_nonneg_left tn (sq_nonneg (n:ℝ))]
  calc _ = ((n:ℝ)^2*(T+1)*3)*Real.exp (-(c*n)) := by ring
       _ ≤ Real.exp (c/2*n)*Real.exp (-(c*n)) := mul_le_mul_of_nonneg_right (poly.trans pen) (Real.exp_nonneg _)
       _ = _ := by rw [←Real.exp_add]; congr 1; ring

theorem todos_los_absorbedores_hasta_el_corte (κ m ζ C γ : ℝ≥0) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (gp : 0<γ) :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,∀ n≥N,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
    ControlEspacial p κ m L → BalanceMalla n h p C → ∀ T≤2*n-1,ζ≤fraccionAntes n T →
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    let ini:=fun z j => blancoDeLaRaiz ((j:ℝ≥0)/(↑(2*n-1):ℝ≥0)) z (cargaDeDestino h p z) (probDeLaCasilla h p)
    (avg masas (rutas S 0 T (initial n h)) (mark masas (fun l => ∃ z,∃ j≤T,(γ:ℝ)*n≤
      |(physicalCount (estadoEn (initial n h) l j).physical z:ℝ)-((ini z j):ℝ)|))).val ≤Real.exp (-(c*n)) := by
  obtain ⟨c,cp,N₁,point⟩:=cuenta_directa_hasta_el_corte κ m ζ C γ kp m1 zp gp
  obtain ⟨N₂,poly⟩:=absorber_raices_y_tiempos c cp
  refine ⟨c/2,by positivity,max N₁ N₂,?_⟩
  intro n hn h hh p L sp bal T cut fl S ini
  let b:ℝ≥0:=⟨3*Real.exp (-(c*n)),by positivity⟩
  let event:=fun z j (l : List (State n)) => (γ:ℝ)*n≤|(physicalCount (estadoEn (initial n h) l j).physical z:ℝ)-((ini z j):ℝ)|
  have each (z : Cell n) (j : ℕ) (jt : j≤T) := point n (by omega) h hh p L sp bal j (jt.trans cut)
    (fraccion_antes_del_horizonte jt fl) z
  have rec (v : ℝ≥0) (hv : v≠masas.zero) : masas.mul v⁻¹ v=masas.one := inv_mul_cancel₀ hv
  have pos (i j : ℕ) (ne : i+j≠0) : masas.add (ns masas i) (ns masas j)≠masas.zero := by
    rw [ns_real,ns_real]; change (i:ℝ≥0)+j≠0; rw [←Nat.cast_add]; exact_mod_cast ne
  have combined:=union_de_raices_y_horizontes n T (initial n h) S (kernel_total masas _ _ rec pos)
    event b (fun z j jt => NNReal.coe_le_coe.mp (each z j jt))
  have take (l : List (State n)) (j : ℕ) : estadoEn (initial n h) (l.take j) j=estadoEn (initial n h) l j := by
    simp [estadoEn,List.take_take]
  simp only [event,take] at combined
  exact (NNReal.coe_le_coe.mpr combined).trans (by simpa only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,
    NNReal.coe_pow,NNReal.coe_natCast,b] using poly n (by omega) T (by omega))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.todos_los_absorbedores_hasta_el_corte
