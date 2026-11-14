import RegularidadDeLosFactoresPorTraslacion
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Topology
theorem constante_comun_en_una_banda_del_normalizador {lo hi κ M m : ℝ}
    (lp : 0<lo) (kp : 0<κ) (mp : 0<m) :
    ∃ L : ℝ,0≤L ∧ ∀ x∈Icc (0:ℝ) (1/2),∀ b∈Icc lo hi,constanteTraslacionB33 x b κ M m≤L := by
  let S:=Icc (0:ℝ) (1/2) ×ˢ Icc lo hi
  let f:=fun z : ℝ×ℝ=>constanteTraslacionB33 z.1 z.2 κ M m
  have cont : ContinuousOn f S := by
    intro z hz
    have xn : 0≤z.1 := hz.1.1
    have bp : 0<z.2 := lp.trans_le hz.2.1
    have e1 : 0<z.1+z.2 := by positivity
    have e2 : 0<z.1+z.2*κ^2 := by positivity
    have e3 : 0<min (cotaInferiorDensidadB33 z.1 z.2 m κ/2) (κ/5) := by
      unfold cotaInferiorDensidadB33
      apply lt_min <;> positivity
    apply ContinuousAt.continuousWithinAt
    dsimp only [f,constanteTraslacionB33,techoDeLosCuatroB33,cotaInferiorDensidadB33] at *
    fun_prop (disch := first | exact e1.ne' | exact e2.ne' | exact e3.ne' | norm_num)
  obtain ⟨B,bound⟩:= (isCompact_Icc.prod isCompact_Icc).bddAbove_image (K:=S) cont
  refine ⟨max B 0,le_max_right ..,?_⟩
  intro x hx b hb
  exact (bound (mem_image_of_mem f (show (x,b)∈S from ⟨hx,hb⟩))).trans (le_max_left ..)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.constante_comun_en_una_banda_del_normalizador
