import EntropiaEnElCuadradoCentrado
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped ENNReal

def medidaDelPerfil (P : TableroMedido) := cuadrado.withDensity (fun z => (P.ν z:ℝ≥0∞))

/-- Probability mass and the four marginal conditions in translated square coordinates. -/
def admisibleParaConteo (P : TableroMedido) : Prop :=
  P.rho=1 ∧ (∀ i : Fin 4, (i.val < 2) → Measure.map (coord i) (medidaDelPerfil P)=marginalRef i) ∧
  (∀ i : Fin 4, (2 ≤ i.val) → Measure.map (coord i) (medidaDelPerfil P)≤marginalRef i)

theorem perfil_lleno_admisible {P p b} (h : EulerFisica P p 0 b) : admisibleParaConteo P := by
  refine ⟨by simpa using h.masa,?_,?_⟩
  · intro i rc
    change Measure.map (coord i) (cuadrado.withDensity _)=_
    rw [P.ley.imagen i]
    refine (withDensity_congr_ae (g:=(1:ℝ→ℝ≥0∞)) ?_).trans withDensity_one
    apply (vacancia_transversal_llena h i rc).mono
    intro s hs
    have realval : (P.m i s:ℝ)=1 := by dsimp [TableroMedido.u] at hs; linarith
    have val : P.m i s=1 := NNReal.coe_injective (by simpa using realval)
    change (P.m i s:ℝ≥0∞)=1
    simp [val]
  · intro i _
    change Measure.map (coord i) (cuadrado.withDensity _)≤_
    rw [P.ley.imagen i]
    calc _ ≤ (marginalRef i).withDensity 1 := by
          apply withDensity_mono
          apply (P.admisible i).mono
          intro s hs
          have val : P.m i s≤1 := by exact_mod_cast hs
          change (P.m i s:ℝ≥0∞)≤1
          exact_mod_cast val
         _ = _ := withDensity_one

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.perfil_lleno_admisible
