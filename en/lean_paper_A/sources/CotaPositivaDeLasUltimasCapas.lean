import PerfilDeMallaBajoLaLeyUniforme
import UmbralEspacialParaHuecosFijos
import ProbabilidadDeCrucesBuenos
import BalanceDeLaRamaEnTodasLasRaices
import RetiradaDeReinas
open Filter Set
open scoped NNReal Topology
namespace ArticuloA.Historias
open Perfil Limites
noncomputable section

theorem piso_de_completabilidad {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b)
    (ext : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0)))
    (h : ℕ) (hh : 0<h) :
    (κ/2)^4 ≤ liminf (fun n => fracReal n h) atTop := by
  obtain ⟨C,balance⟩:=balance_de_la_rama_puntual rama pt
  let a:=(fun (n : ℕ) => blancoNormalizado (n:=n) h (p ((h:ℝ)/n)))
  have direct (η : ℝ) (ep : 0<η) := directa_de_la_rama rama h ext (fun _ => h)
    (Eventually.of_forall (fun _ => le_rfl)) C (balance h) η ep
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 zero
  have lower:=ext (admisibilidad_del_lleno full)
  rw [normalizacion_de_simkin full (rama.espacio 0 zero) rama.kp rama.lp] at lower
  have sol:=soluciones_eventuales_del_primer_orden (conteo_local_implica_primer_orden lower)
  have nonempty : ∀ᶠ n : ℕ in atTop,0<count n (n-h) := by
    filter_upwards [sol,eventually_ge_atTop h] with n s big
    exact capa_positiva_si_hay_solucion big s
  have upper : ∀ᶠ n : ℕ in atTop,fracReal n h≤1 := by
    filter_upwards [nonempty,eventually_ge_atTop h] with n pos big
    have co:=Capas.una_retirada n h hh big
    rw [show n-(h-1)=n-h+1 by omega] at co
    unfold fracReal
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast co
  have non : ∀ n : ℕ,0≤fracReal n h := by intro n; unfold fracReal; positivity
  apply (le_liminf_iff (isCoboundedUnder_ge_of_eventually_le _ upper)
    (show atTop.IsBoundedUnder (· ≥ ·) (fun n => fracReal n h) from isBoundedUnder_of ⟨0,non⟩)).mpr
  intro y hy
  have cp : 0<(κ/2)^4 := pow_pos (half_pos rama.kp) _
  obtain ⟨z,lo,hi⟩:=exists_between (max_lt cp hy)
  have zp : 0<z := (le_max_left ..).trans_lt lo
  have yz : y<z := (le_max_right ..).trans_lt lo
  exact positividad_desde_malla h hh a z zp nonempty
    (piso_eventual_de_las_raices rama h C (balance h) z hi) direct y yz

/-- The explicit bound of Article A, including the shared eventual lower bound on both layers. -/
theorem dos_ultimas_capas_del_articulo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b)
    (ext : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0))) :
    let a₀:=(κ/2)^4/16
    (∀ h : ℕ,h=1 ∨ h=2 → a₀/2 ≤ liminf (fun n => fracReal n h) atTop) ∧
    (∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2) := by
  intro a₀
  have cp : 0<(κ/2)^4 := pow_pos (half_pos rama.kp) _
  have slack : a₀/2<(κ/2)^4 := by dsimp [a₀]; linarith
  constructor
  · intro h hs; exact slack.le.trans (piso_de_completabilidad rama pt ext h (by omega))
  · have pos : 0<a₀/2 := by dsimp [a₀]; positivity
    have one:=(slack.trans_le (piso_de_completabilidad rama pt ext 1 (by decide)))
    have two:=(slack.trans_le (piso_de_completabilidad rama pt ext 2 (by decide)))
    have non (h : ℕ) : atTop.IsBoundedUnder (· ≥ ·) (fun n => fracReal n h) :=
      isBoundedUnder_of ⟨0,fun n => by change 0≤fracReal n h; unfold fracReal; positivity⟩
    refine ⟨a₀/2,pos,?_⟩
    filter_upwards [eventually_lt_of_lt_liminf one (non 1),eventually_lt_of_lt_liminf two (non 2)] with n hn₁ hn₂
    exact ⟨hn₁.le,hn₂.le⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_ultimas_capas_del_articulo
