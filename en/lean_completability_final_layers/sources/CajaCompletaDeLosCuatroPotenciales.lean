import MinimizadorPorLaBrechaDePuntoMedio
import Mathlib.MeasureTheory.Function.LpSpace.Complete
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped Topology
abbrev PotencialesL2 := (i : Fin 4)→Lp ℝ 2 (marginalRef i)

def cajaDePotenciales (H : ℝ) : Set PotencialesL2 :=
  {u | ∀ i,∀ᵐ s ∂marginalRef i, u i s∈Icc 0 H}

private theorem caja_componente_cerrada (H : ℝ) (hp : 0≤H) (i : Fin 4) :
    IsClosed {u : Lp ℝ 2 (marginalRef i) | ∀ᵐ s ∂marginalRef i,u s∈Icc 0 H} := by
  let proj (t : ℝ):=min (max t 0) H
  have lip : LipschitzWith 1 proj := (LipschitzWith.id.max_const 0).min_const H
  have zero : proj 0=0 := by simp [proj,hp]
  let T : Lp ℝ 2 (marginalRef i)→Lp ℝ 2 (marginalRef i):=lip.compLp zero
  have setEq : {u : Lp ℝ 2 (marginalRef i) | ∀ᵐ s ∂marginalRef i,u s∈Icc 0 H}={u | T u=u} := by
    ext u
    constructor
    · intro hu; apply Lp.ext
      filter_upwards [lip.coeFn_compLp zero u,hu] with s hs hr
      exact hs.trans (by simp [proj,max_eq_left hr.1,min_eq_left hr.2])
    · intro hu
      have eq:=lip.coeFn_compLp zero u
      change T u=u at hu
      change ⇑(T u)=ᵐ[marginalRef i] proj ∘ u at eq
      rw [hu] at eq
      filter_upwards [eq] with s hs
      exact hs.symm ▸ (show proj (u s)∈Icc 0 H from ⟨le_min (le_max_right _ _) hp,min_le_right _ _⟩)
  rw [setEq]; exact isClosed_eq (lip.continuous_compLp zero) continuous_id

theorem caja_de_potenciales_cerrada {H : ℝ} (hp : 0≤H) : IsClosed (cajaDePotenciales H) := by
  have eq : cajaDePotenciales H=⋂ i : Fin 4,{u : PotencialesL2 | ∀ᵐ s ∂marginalRef i,u i s∈Icc 0 H} := by
    ext u; simp [cajaDePotenciales]
  rw [eq]; apply isClosed_iInter; intro i
  exact (caja_componente_cerrada H hp i).preimage (show Continuous (fun u : PotencialesL2=>u i) from continuous_apply i)

theorem caja_de_potenciales_completa {H : ℝ} (hp : 0≤H) : CompleteSpace (cajaDePotenciales H) :=
  (caja_de_potenciales_cerrada hp).completeSpace_coe

theorem cero_pertenece_a_la_caja {H : ℝ} (hp : 0≤H) : (0 : PotencialesL2)∈cajaDePotenciales H := by
  intro i
  filter_upwards [Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=marginalRef i)] with s hs
  change (0 : Lp ℝ 2 (marginalRef i)) s∈Icc 0 H
  rw [hs]; exact ⟨le_rfl,hp⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.caja_de_potenciales_cerrada
#print axioms ArticuloA.Historias.caja_de_potenciales_completa
#print axioms ArticuloA.Historias.cero_pertenece_a_la_caja
