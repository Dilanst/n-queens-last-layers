import DelCorteInversoAlUltimoReloj
import ColaFisicaUniformeAntesDelCorte
import EleccionDeLaVentanaTerminal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto
theorem concentracion_inversa_de_E2_completo (κ m C ε : ℝ≥0) (W : ℝ) (wp : 0≤W) (kp : 0<κ) (m1 : 1≤m) (ep : 0<ε) :
    ∃ c : ℝ,0<c ∧ ∃ n₀ : ℕ,∀ n≥n₀,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
    ControlEspacial p κ m L → BalanceMalla n h p C → ∀ w : Cell n→ℝ,(∀ e,|w e|≤W) →
    let N:=2*n-1
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    (avg masas (rutas S 0 N (initial n h)) (mark masas (fun l =>
      (ε:ℝ)*(n:ℝ)^2≤|inversasDelTablero (estadoEn (initial n h) l N).physical w-blancoInverso h p w 1|))).val
        ≤3*Real.exp (-(c*(n:ℝ))) := by
  let γ:ℝ≥0:=ε/2
  have gp : 0<γ := by dsimp [γ]; positivity
  have gr : (γ:ℝ)=(ε:ℝ)/2 := rfl
  obtain ⟨d,dlarge⟩:=exists_nat_gt (20*W/(γ:ℝ))
  let k:=max 2 d
  have k2 : 2≤k := le_max_left .. 
  have kpos : 0<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have cost : 20*W/(k:ℝ)≤γ := by
    have room : 20*W/(γ:ℝ)≤(k:ℝ) := dlarge.le.trans (by exact_mod_cast le_max_right 2 d)
    exact (div_le_iff₀ kpos).mpr (by simpa [mul_comm] using (div_le_iff₀ (NNReal.coe_pos.mpr gp)).mp room)
  let ζ:ℝ≥0:=(k:ℝ≥0)⁻¹
  have zp : 0<ζ := inv_pos.mpr (by exact_mod_cast kpos)
  obtain ⟨c,cp,N₁,tail⟩:=cola_uniforme_del_inverso_original κ m ζ C γ W wp kp m1 zp gp
  obtain ⟨N₂,large⟩:=exists_nat_gt (2*(C:ℝ)/(κ:ℝ))
  refine ⟨c,cp,max (max N₁ k) N₂,?_⟩
  intro n hn h hh p L space bal w cap N S
  have kn : k≤n := by omega
  have nn : 2≤n := k2.trans kn
  have margin : 2*(C:ℝ)≤κ*n := by
    have r:=large.le.trans (show (N₂:ℝ)≤n by exact_mod_cast (by omega : N₂≤n))
    simpa [mul_comm] using (div_le_iff₀ (NNReal.coe_pos.mpr kp)).mp r
  let T:=N-restoDelReloj N k
  obtain ⟨tp,fl,db,yb,rd⟩:=ventana_final n k k2 kn
  let y:=horizonteInverso n T 0
  have dy : 1-(y:ℝ)≤2/(k:ℝ) := by simpa only [y,horizonteInverso,Nat.sub_zero,NNReal.coe_div,NNReal.coe_natCast] using yb
  have dr : (↑(N-T):ℝ)≤4*(n:ℝ)/k := by rw [rd]; exact db
  have costs : γ*(n:ℝ)^2+4*(n:ℝ)*(↑(N-T):ℝ)*W+2*(1-(y:ℝ))*W*(n:ℝ)^2≤(ε:ℝ)*(n:ℝ)^2 := by
    have time : 4*(n:ℝ)*(↑(N-T):ℝ)*W≤4*n*(4*(n:ℝ)/k)*W := by gcongr
    have tar : 2*(1-(y:ℝ))*W*(n:ℝ)^2≤2*(2/(k:ℝ))*W*(n:ℝ)^2 := by gcongr
    have id : 4*n*(4*(n:ℝ)/k)*W+2*(2/(k:ℝ))*W*(n:ℝ)^2=(20*W/k)*(n:ℝ)^2 := by ring
    have total:=(add_le_add time tar).trans_eq id
    have bound:=total.trans (mul_le_mul_of_nonneg_right cost (sq_nonneg (n:ℝ)))
    rw [gr] at bound ⊢; linarith only [bound]
  let bad:=fun (r : ℝ) (l : List (State n)) => r≤
    |inversasDelTablero (estadoEn (initial n h) l N).physical w-blancoInverso h p w 1|
  have sub:=misma_masa_en_el_soporte (rutas S 0 N (initial n h)) (bad ((ε:ℝ)*n^2)) (bad _) (by
    intro i _ _ hit; exact costs.trans hit)
  have cut:=control_del_inverso_en_el_ultimo_reloj nn tp space kp bal margin w wp cap γ
  exact (NNReal.coe_le_coe.mpr (sub.trans cut)).trans (tail n (by omega) h hh p L space bal T tp fl w cap)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.concentracion_inversa_de_E2_completo
