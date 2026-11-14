import CotaPositivaDeLasUltimasCapas
open Filter Set
namespace ArticuloA.Historias
open Perfil Limites
noncomputable section

/-- The lower count interface used in the entropy comparison asks only for a dominated count.
It imposes no neighborhood condition on its witness. -/
theorem conteo_equivalente_al_primer_orden (s : ℝ) :
    ConteoLocalInferior s ↔ CotaDePrimerOrden s := by
  refine ⟨conteo_local_implica_primer_orden,?_⟩
  intro first ε ep
  refine ⟨fun n => count n n,fun _ => le_rfl,?_⟩
  filter_upwards [first ε ep,soluciones_eventuales_del_primer_orden first] with n h hn
  simpa only [Real.exp_log (by exact_mod_cast hn : 0<(count n n:ℝ))]
    using Real.exp_le_exp.mpr h

/-- For applications it suffices to supply the global first-order lower bound
in centered coordinates, independently of the eventual hole count. -/
theorem completabilidad_desde_primer_orden {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b) (primero : CotaDePrimerOrden (valorCentrado (P 0))) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2 :=
  (dos_ultimas_capas_del_articulo rama pt (fun _ => (conteo_equivalente_al_primer_orden _).mpr primero)).2
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.completabilidad_desde_primer_orden
