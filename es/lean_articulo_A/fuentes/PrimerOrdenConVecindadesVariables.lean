import DelConteoLocalDeSimkinAlGlobal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Filter Limites Perfil
open scoped Topology
/-- The neighborhood and its finite set of boards can depend on the requested tolerance. -/
theorem primer_orden_desde_vecindades_variables {s : ℝ}
    (locales : ∀ η : ℝ, 0<η → ∃ S : (n : ℕ) → Finset (Placement n),
      (∀ n,S n⊆nivel n n) ∧ Real.exp (s-η)≤liminf (raizDelConteo (fun n => (S n).card)) atTop) :
    CotaDePrimerOrden s := by
  intro ε hε
  have hp : 0<ε/2 := half_pos hε
  obtain ⟨S,hs,hlim⟩:=locales (ε/2) hp
  have lower:=desde_el_liminf_local (s-ε/2) S hs hlim (ε/2) hp
  filter_upwards [lower] with n hn
  linarith only [hn]

theorem primer_orden_de_euler_con_tolerancias {P p b}
    (h : EulerFisica P p 0 b)
    (locales : admisibleParaConteo P → ∀ η : ℝ, 0<η →
      ∃ S : (n : ℕ) → Finset (Placement n), (∀ n,S n⊆nivel n n) ∧
        Real.exp (valorCentrado P-η)≤liminf (raizDelConteo (fun n => (S n).card)) atTop) :
    CotaDePrimerOrden (valorCentrado P) :=
  primer_orden_desde_vecindades_variables (locales (perfil_lleno_admisible h))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.primer_orden_desde_vecindades_variables
#print axioms ArticuloA.Historias.primer_orden_de_euler_con_tolerancias
