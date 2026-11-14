import CotaYExtremosDesdeLaMedida
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

open Perfil Set MeasureTheory
open scoped Interval
variable {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ} {κ M L : ℝ}

theorem normalizacion_transversal_en_el_lleno
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (space : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) (lp : 0≤L)
    (cont : ContinuidadEnElLleno p b) (i : Fin 4) (rc : i.val<2) :
    (∫ t in (0:ℝ)..1,(factorF (p 0) i t:ℝ))=1 := by
  let intg (x : ℝ):=∫ t in (0:ℝ)..1,(factorF (p x) i t:ℝ)
  change intg 0=1
  have dom : rangoF i=Icc (0:ℝ) 1 := by
    have or : i=0 ∨ i=1 := by omega
    rcases or with rfl|rfl <;> rfl
  have closed (x : ℝ) (hx : x∈Icc 0 (1/2:ℝ)) :
      IntervalIntegrable (fun t => (factorF (p x) i t:ℝ)) volume 0 1 := by
    have c:=continua_de_cota lp (regular_familia (space x hx) i).oscilacion
    rw [dom] at c
    exact c.intervalIntegrable_of_Icc zero_le_one
  by_contra bad
  let g:=|intg 0-1|
  have gp : 0<g := abs_pos.mpr (sub_ne_zero.mpr bad)
  obtain ⟨d,dp,near⟩:=cont (g/2) (half_pos gp)
  let x:=min (d/2) (1/4:ℝ)
  have xp : 0<x := lt_min (half_pos dp) (by norm_num)
  have hx : x∈Icc 0 (1/2:ℝ) := ⟨xp.le,(min_le_right _ _).trans (by norm_num)⟩
  have xsmall : x<d := (min_le_left _ _).trans_lt (half_lt_self dp)
  have xo : intg x=1 := masa_transversal_reescalada (eq x hx) (Real.toNNReal_pos.mpr xp) i rc
  have hi : |intg x-intg 0|≤g/2 := by
    dsimp only [intg]
    rw [← intervalIntegral.integral_sub (closed x hx) (closed 0 ⟨le_rfl,by norm_num⟩)]
    have ub:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=1)
      (f:=fun t => (factorF (p x) i t:ℝ)-(factorF (p 0) i t:ℝ)) (C:=g/2) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        exact (near _ hx xsmall).2 i t (dom ▸ ⟨ht.1.le,ht.2⟩))
    simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using ub
  rw [xo,abs_sub_comm] at hi
  exact (not_le.mpr (half_lt_self gp)) hi

theorem construir_rama_desde_la_euler_medida (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (space : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (cont : ContinuidadEnElLleno p b) : RamaDensa P p b κ M L (1/κ^4) := by
  refine ⟨kp,k1,m1,lp,eq,space,fun x hx => techo_desde_la_masa (eq x hx) (space x hx) kp,
    fun x hx => vacancia_en_los_extremos (eq x hx) (space x hx) lp,?_⟩
  intro x hx
  have one (i : Fin 4) (rc : i.val<2) : (∫ t in (0:ℝ)..1,(factorF (p x) i t:ℝ))=1 := by
    by_cases z : x=0
    · subst x; exact normalizacion_transversal_en_el_lleno eq space lp cont i rc
    · exact masa_transversal_reescalada (eq x hx) (Real.toNNReal_pos.mpr (lt_of_le_of_ne hx.1 (Ne.symm z))) i rc
  exact ⟨one 0 (by decide),one 1 (by decide)⟩

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_transversal_en_el_lleno
#print axioms ArticuloA.Historias.construir_rama_desde_la_euler_medida
