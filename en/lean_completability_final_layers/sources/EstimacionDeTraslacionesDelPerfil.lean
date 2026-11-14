import RamaMedidaConNormalizacionDeducida
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
/-- Translation argument of Appendix A2, at a fixed density.
    The normalization parameter b is the same in the two equations. -/
theorem comparacion_de_los_factores_trasladados
    {d b J Jt y yt error E V t B K lam d₀ bMax : ℝ}
    (floor : 0<d₀) (coerc : 0<lam) (boundB : 0≤B) (boundK : 0≤K)
    (db : |b|≤bMax) (orig : y*(d+b*J)=1) (moved : yt*(d+b*Jt)=1+error)
    (d1 : d₀≤d+b*J) (d2 : d₀≤d+b*Jt)
    (res : |error|≤2*B*|t|) (norm : E≤2*Real.sqrt 5*B*|t|)
    (anchor : lam*V≤E) (fiber : |Jt-J|≤Real.sqrt 3*K^3*V) :
    |yt-y|≤(2*B/d₀+2*Real.sqrt 15*bMax*K^3*B/(d₀^2*lam))*|t| := by
  let D:=d+b*J
  let Dt:=d+b*Jt
  have posD : 0<D := floor.trans_le d1
  have posT : 0<Dt := floor.trans_le d2
  have eq : yt-y=error/Dt+b*(J-Jt)/(Dt*D) := by
    have a : yt=(1+error)/Dt := (eq_div_iff posT.ne').mpr moved
    have b' : y=1/D := (eq_div_iff posD.ne').mpr orig
    rw [a,b']; field_simp [posD.ne',posT.ne']; dsimp [D,Dt]; ring
  have vv : V≤(2*Real.sqrt 5*B*|t|)/lam := (le_div_iff₀ coerc).mpr (by linarith [anchor,norm])
  have root : Real.sqrt 3*Real.sqrt 5=Real.sqrt 15 := by
    rw [←Real.sqrt_mul (by norm_num : (0:ℝ)≤3)]; norm_num
  have fd : d₀^2≤Dt*D := by rw [pow_two]; exact mul_le_mul d2 d1 floor.le posT.le
  have first : |error/Dt|≤(2*B*|t|)/d₀ := by
    rw [abs_div,abs_of_pos posT]
    exact div_le_div₀ (by positivity) res floor d2
  have second : |b*(J-Jt)/(Dt*D)|≤
      (bMax*(Real.sqrt 3*K^3*((2*Real.sqrt 5*B*|t|)/lam)))/d₀^2 := by
    rw [abs_div,abs_mul,abs_of_pos (mul_pos posT posD),abs_sub_comm J Jt]
    apply div_le_div₀ _ _ (sq_pos_of_pos floor) fd
    · have bm : 0≤bMax := (abs_nonneg b).trans db
      positivity
    · exact mul_le_mul db (fiber.trans (mul_le_mul_of_nonneg_left vv (by positivity)))
        (abs_nonneg _) ((abs_nonneg b).trans db)
  rw [eq]
  apply (abs_add_le ..).trans ((add_le_add first second).trans_eq _)
  rw [←root]
  ring

theorem lipschitz_desde_incrementos_espaciales {f : ℝ→ℝ} {D : Set ℝ} {M : ℝ≥0}
    (step : ∀ r∈D,∀ t : ℝ,r+t∈D → |f (r+t)-f r|≤(M:ℝ)*|t|) :
    LipschitzOnWith M f D := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  simpa [Real.dist_eq,abs_sub_comm] using step s hs (r-s) (by simpa using hr)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparacion_de_los_factores_trasladados
#print axioms ArticuloA.Historias.lipschitz_desde_incrementos_espaciales
