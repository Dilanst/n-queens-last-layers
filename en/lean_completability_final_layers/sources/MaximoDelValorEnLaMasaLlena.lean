import RamaCompletaConElMismoExtremo
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open private normalizacion_como_integral_de_intervalo in control_comun_desde_una_rama_medida

/-- The comparison holds for every measured board of mass one with integrable entropies,
    even if one of its slacks vanishes. -/
theorem el_perfil_lleno_domina_a_cada_competidor {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (kp : 0<κ) (mm : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) (g : NormalizacionR15 (p 0))
    (Q : TableroMedido) (mass : Q.rho=1) (qi : Integrable (fun z=>xlogx (Q.ν z)) cuadrado)
    (ui : ∀ i,Integrable (fun t=>xlogx (Q.u i t)) (marginalRef i)) : Q.s≤(P 0).s := by
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ):=⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0):=by simpa using eq 0 z
  let β:=1/(2*M^4)
  have mp : 0<M:=zero_lt_one.trans_le mm
  have bp : 0<β:=by dsimp [β]; positivity
  let C:=|2+log (b 0)-log β|+1
  have cp : 0<C:=by dsimp [C]; positivity
  by_contra! gt
  let gap:=Q.s-(P 0).s
  have gp : 0<gap:=sub_pos.mpr gt
  let x:=min (1/2:ℝ) (gap/(2*C))
  have xp : 0<x:=lt_min (by norm_num) (div_pos gp (by positivity))
  have xh : x≤1/2:=min_le_left _ _
  have ok : x∈Icc 0 (1/2:ℝ):=⟨xp.le,xh⟩
  have xe:=Real.coe_toNNReal _ xp.le
  have part:=eq x ok
  have pos:=Real.toNNReal_pos.mpr xp
  have small := soporte_del_perfil_positivo part (sp x ok) kp lp pos Q qi ui
  have upper := cota_superior_desde_el_lleno full part (sp 0 z) (sp x ok) kp lp pos
    (normalizacion_como_integral_de_intervalo g 0 (by decide))
    (normalizacion_como_integral_de_intervalo g 1 (by decide))
  rw [mass,part.masa,xe,Real.log_div part.coef.ne' (pow_ne_zero 2 xp.ne'),Real.log_pow] at small
  norm_num1 at small
  rw [xe] at upper
  have lower : β≤b x:=cota_inferior_del_coeficiente part (sp x ok) kp mm (by rwa [xe])
  have logs:=mul_le_mul_of_nonneg_left (Real.log_le_log bp lower) xp.le
  have bound : gap≤x*(2+log (b 0)-log β) := by dsimp only [gap]; nlinarith only [small,upper,logs]
  have cap : 2+log (b 0)-log β≤C:=by dsimp [C]; linarith only [le_abs_self (2+log (b 0)-log β)]
  have half := (le_div_iff₀ (show 0<2*C by positivity)).mp (min_le_right (1/2:ℝ) (gap/(2*C)))
  have last := bound.trans (mul_le_mul_of_nonneg_left cap xp.le)
  change x*(2*C)≤gap at half
  linarith only [last,half,gp]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.el_perfil_lleno_domina_a_cada_competidor
