import ConcentracionFisicaEnElUltimoReloj
import EleccionDeLaVentanaTerminal
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem todos_los_cruces_al_final_de_E2 (κ m C ε : ℝ≥0) (kp : 0<κ) (m1 : 1≤m) (ep : 0<ε) :
    ∃ c : ℝ,0<c ∧ ∃ n₀ : ℕ,∀ n≥n₀,∀ h≤n,∀ p : FactoresContinuos,∀ L : ℝ,
    ControlEspacial p κ m L → BalanceMalla n h p C →
    let N:=2*n-1
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    (avg masas (rutas S 0 N (initial n h)) (mark masas (fun l => ∃ z,
      (ε:ℝ)*n≤|(physicalCount (estadoEn (initial n h) l N).physical z:ℝ)-(blancoFinalDeMalla h p z:ℝ)|))).val
      ≤Real.exp (-(c*n)) := by
  let M:ℝ≥0:=m^4/κ^4
  let γ:ℝ≥0:=ε/2
  have gr : (γ:ℝ)=(ε:ℝ)/2 := rfl
  have gp : 0<γ := div_pos ep (by norm_num)
  obtain ⟨d,dlarge⟩:=exists_nat_gt ((16+2*(M:ℝ))/(γ:ℝ))
  let k:=max 2 d
  have kp' : 0<(k:ℝ) := by exact_mod_cast (by dsimp [k]; omega : 0<k)
  have budget : 16+2*(M:ℝ)≤(γ:ℝ)*k := by
    have fit : (16+2*(M:ℝ))/(γ:ℝ)≤(k:ℝ) := dlarge.le.trans (by exact_mod_cast (by dsimp [k]; omega : d≤k))
    simpa [mul_comm] using (div_le_iff₀ (NNReal.coe_pos.mpr gp)).mp fit
  let ζ:ℝ≥0:=(k:ℝ≥0)⁻¹
  have zp : 0<ζ := inv_pos.mpr (by exact_mod_cast kp')
  obtain ⟨c,cp,N₁,tail⟩:=todos_los_absorbedores_hasta_el_corte κ m ζ C γ kp m1 zp gp
  obtain ⟨N₂,N₂big⟩:=exists_nat_gt (2*(C:ℝ)/(κ:ℝ))
  refine ⟨c,cp,max (max k N₁) N₂,?_⟩
  intro n hn h hh p L sp bal N S
  have kn : k≤n := by omega
  have nn : 2≤n := (le_max_left 2 d).trans kn
  have big : 2*(C:ℝ)≤(κ:ℝ)*n := by
    have room := N₂big.le.trans (show (N₂:ℝ)≤n by exact_mod_cast (by omega : N₂≤n))
    simpa [mul_comm] using (div_le_iff₀ (NNReal.coe_pos.mpr kp)).mp room
  let T:=N-restoDelReloj N k
  obtain ⟨tp,zp',db,yb,rd⟩:=ventana_final n k (le_max_left ..) kn
  have load (z : Cell n) := cargas_para_un_cruce nn sp kp bal big z
  let y:ℝ≥0:=(T:ℝ≥0)/N
  have tol : (γ:ℝ)*n+4*(↑(N-T):ℝ)+(1-(y:ℝ))*M*n≤(ε:ℝ)*n := by
    change 1-(T:ℝ)/N≤_ at yb
    have dy : 1-(y:ℝ)≤2/(k:ℝ) := yb
    have dr : (↑(N-T):ℝ)≤4*(n:ℝ)/k := by rw [rd]; exact db
    have term:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right dy M.property) (Nat.cast_nonneg n)
    have cost : (16+2*(M:ℝ))/k≤γ := (div_le_iff₀ kp').mpr budget
    have sum : 4*(4*(n:ℝ)/k)+(2/(k:ℝ))*(M:ℝ)*n=((16+2*(M:ℝ))/k)*n := by ring
    have a := mul_le_mul_of_nonneg_right cost (Nat.cast_nonneg n)
    rw [←sum] at a
    calc _ = (γ:ℝ)*n+(4*(↑(N-T):ℝ)+(1-(y:ℝ))*M*n) := add_assoc _ _ _
         _ ≤ (γ:ℝ)*n+(γ:ℝ)*n := add_le_add_left ((add_le_add (mul_le_mul_of_nonneg_left dr (by norm_num : (0:ℝ)≤4)) term).trans a) _
         _ = _ := by rw [gr]; ring
  let bad := fun (r : ℝ) (l : List (State n)) => ∃ z,
    r≤|(physicalCount (estadoEn (initial n h) l N).physical z:ℝ)-(blancoFinalDeMalla h p z:ℝ)|
  have sub:=misma_masa_en_el_soporte (rutas S 0 N (initial n h)) (bad ((ε:ℝ)*n)) (bad _) (by
    rintro _ _ _ ⟨z,hz⟩; exact ⟨z,tol.trans hz⟩)
  have cut:=control_final_con_corte_fijo (n:=n) (T:=T) (h:=h) p γ M tp (by omega : 0<2*n-1)
    (fun z => (load z).1) (fun e => ((load e).2 e))
  exact (NNReal.coe_le_coe.mpr (sub.trans cut)).trans (tail n (by omega) h hh p L sp bal T tp zp')

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.todos_los_cruces_al_final_de_E2
