import EstimacionDeTraslacionesDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
def distanciaEnMedida {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b : X→ℝ) :=
  ∫ t,|a t-b t| ∂μ

def distanciaTableros (P Q : TableroMedido) := distanciaEnMedida cuadrado (fun z=>(P.ν z:ℝ)) (fun z=>(Q.ν z:ℝ))

theorem dualidad_de_la_diferencia (P Q : TableroMedido) (i : Fin 4) (w : ℝ→ℝ) (mw : Measurable w)
    (bound : ∃ C : ℝ,∀ s,‖w s‖≤C) :
    (∫ s,((P.m i s:ℝ)-Q.m i s)*w s ∂marginalRef i)=
    ∫ z,((P.ν z:ℝ)-Q.ν z)*w (coord i z) ∂cuadrado := by
  have line (T : TableroMedido) : Integrable (fun s=>(T.m i s:ℝ)*w s) (marginalRef i) := by
    simpa only [mul_comm] using (T.m_integrable i).bdd_mul mw.aestronglyMeasurable bound
  have area (T : TableroMedido) : Integrable (fun z=>(T.ν z:ℝ)*w (coord i z)) cuadrado := by
    simpa only [mul_comm] using T.masaFinita.bdd_mul (mw.comp (coord_medible i)).aestronglyMeasurable
      ⟨bound.choose,fun z=>bound.choose_spec (coord i z)⟩
  simp_rw [sub_mul]
  rw [integral_sub (line P) (line Q),integral_sub (area P) (area Q),adjuncion P.ley i w mw,adjuncion Q.ley i w mw]

theorem contraccion_marginal_en_L1 (P Q : TableroMedido) (i : Fin 4) :
    distanciaEnMedida (marginalRef i) (fun s=>(P.m i s:ℝ)) (fun s=>(Q.m i s:ℝ))≤distanciaTableros P Q := by
  let w:=fun s=>if (Q.m i s:ℝ)≤P.m i s then (1:ℝ) else -1
  have mw : Measurable w := Measurable.ite (measurableSet_le (Q.ley.densidadLinea i).coe_nnreal_real
    (P.ley.densidadLinea i).coe_nnreal_real) measurable_const measurable_const
  have norm (s : ℝ) : ‖w s‖≤1 := by dsimp [w]; split_ifs <;> norm_num
  have sgn (s : ℝ) : |(P.m i s:ℝ)-Q.m i s|=((P.m i s:ℝ)-Q.m i s)*w s := by
    dsimp [w]; split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h),mul_one]
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]; ring
  unfold distanciaEnMedida
  simp_rw [sgn]
  rw [dualidad_de_la_diferencia P Q i w mw ⟨1,norm⟩]
  have integ:=(P.masaFinita.sub Q.masaFinita).bdd_mul (mw.comp (coord_medible i)).aestronglyMeasurable
    ⟨1,fun z=>norm (coord i z)⟩
  apply integral_mono (by simpa only [mul_comm,Pi.sub_apply,Function.comp_apply] using integ) (P.masaFinita.sub Q.masaFinita).abs
  · intro z
    change ((P.ν z:ℝ)-Q.ν z)*w (coord i z)≤|(P.ν z:ℝ)-Q.ν z|
    apply (le_abs_self _).trans
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (norm (coord i z)) (abs_nonneg ((P.ν z:ℝ)-Q.ν z))

theorem contraccion_de_vacancias (P Q : TableroMedido) (i : Fin 4) :
    distanciaEnMedida (marginalRef i) (P.u i) (Q.u i)≤distanciaTableros P Q := by
  simpa [distanciaEnMedida,TableroMedido.u,abs_sub_comm] using contraccion_marginal_en_L1 P Q i
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dualidad_de_la_diferencia
#print axioms ArticuloA.Historias.contraccion_marginal_en_L1
#print axioms ArticuloA.Historias.contraccion_de_vacancias
