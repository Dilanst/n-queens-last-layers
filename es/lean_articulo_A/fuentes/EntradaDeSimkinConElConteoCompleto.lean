import PrimerOrdenConVecindadesVariables
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology
/-- Bastan subconjuntos de soluciones. Si se dispone del primer
orden global y del valor variacional superior, el nivel completo da los testigos. -/
theorem testigo_del_primer_orden_global {s S : ℝ} (le : s≤S)
    (global : exp S≤liminf (raizDelConteo (fun n=>count n n)) atTop) :
    ∀ η : ℝ,0<η → ∃ A : (n : ℕ)→Finset (Placement n),(∀ n,A n⊆nivel n n) ∧
      exp (s-η)≤liminf (raizDelConteo (fun n=>(A n).card)) atTop := by
  intro η ep
  refine ⟨fun n=>nivel n n,fun _=>Finset.Subset.rfl,?_⟩
  simpa only [cardinal_nivel] using (exp_le_exp.mpr ((sub_le_self _ ep.le).trans le)).trans global

theorem entrada_de_simkin_con_constante_variacional {S : ℝ}
    (primerOrden : Tendsto (raizDelConteo (fun n=>count n n)) atTop (𝓝 (exp S)))
    (P : TableroMedido) (comparacion : admisibleParaConteo P → valorCentrado P≤S) :
    admisibleParaConteo P → ∀ η : ℝ,0<η → ∃ A : (n : ℕ)→Finset (Placement n),
      (∀ n,A n⊆nivel n n) ∧ exp (valorCentrado P-η)≤liminf (raizDelConteo (fun n=>(A n).card)) atTop :=
  fun adm=>testigo_del_primer_orden_global (comparacion adm) primerOrden.liminf_eq.ge
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.testigo_del_primer_orden_global
#print axioms ArticuloA.Historias.entrada_de_simkin_con_constante_variacional
