import TransferenciaInversaAlNivelUniforme
import ConsecuenciasDesdeElPerfilYElConteoLocal
import BalanceDeLaRamaEnTodasLasRaices
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Set Perfil Limites
open scoped Topology
theorem inversa_de_la_rama_en_su_malla {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (primero : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h)
    (w : (n : ℕ)→Cell n→ℝ) (W : ℝ) (wp : 0≤W) (cap : ∀ n e,|w n e|≤W) (η : ℝ) (ep : 0<η) :
    Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (w n))
      (blancoInverso (h-1) (p ((↑(h-1):ℝ)/n)) (w n) 1/(n:ℝ)^2) η) atTop (𝓝 0) := by
  let j:=h-1
  have ext:=(conteo_equivalente_al_primer_orden _).mpr primero
  obtain ⟨d,small,cost⟩:=L1_de_la_rama_y_el_conteo rama j (fun _ => ext)
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama (euler_puntual_de_la_rama rama)
  let lo : ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi : ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  apply inversa_uniforme_al_blanco_discreto h hh _ d lo hi C (show 0<lo from rama.kp)
    (show 1≤hi from rama.m1) L W η wp ep w cap small
  filter_upwards [cost,bal j,soluciones_eventuales_del_primer_orden primero,eventually_ge_atTop (2*j+2)] with n kl grid sol big
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have half : (j:ℝ)/n≤1/2 := by
    apply (div_le_iff₀ np).mpr
    have r : 2*(j:ℝ)≤n := by exact_mod_cast (by omega : 2*j≤n)
    linarith
  exact ⟨capa_positiva_si_hay_solucion (by change j≤n; omega) sol,
    rama.espacio _ ⟨by positivity,half⟩,grid,kl j le_rfl⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.inversa_de_la_rama_en_su_malla
