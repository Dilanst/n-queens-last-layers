import ExtremoNormalizadoDeLaRamaInterior
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
def completarEnCero {α : Type*} (f : ℝ→α) (a : α) (x : ℝ) : α := if x=0 then a else f x

theorem extender_rama_desde_el_interior {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Ioc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Ioc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) :
    ∃ (P₀ : TableroMedido) (p₀ : FactoresContinuos) (b₀ : ℝ),NormalizacionR15 p₀ ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (completarEnCero P P₀ x) (completarEnCero p p₀ x)
        x.toNNReal (completarEnCero b b₀ x)) ∧
      ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (completarEnCero p p₀ x) κ M L := by
  let y (j : ℕ) : ℝ:=(1/2)*(1/((j:ℝ)+1))
  have inside j : y j∈Ioc 0 (1/2:ℝ) := by
    have low : 0<((j:ℝ)+1) := by positivity
    have u : 1/((j:ℝ)+1)≤1 := by apply (div_le_iff₀ low).mpr; linarith [(by positivity : (0:ℝ)≤(j:ℝ))]
    exact ⟨mul_pos (by norm_num) (div_pos zero_lt_one low),by dsimp [y]; linarith only [u]⟩
  have z : Tendsto y atTop (𝓝 0) := by
    simpa [y] using ((tendsto_const_nhds (x:=(1/2:ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat)
  have yr j : ((y j).toNNReal:ℝ)=y j := Real.coe_toNNReal _ (inside j).1.le
  obtain ⟨P₀,p₀,b₀,e₀,sp₀,g₀,_,_⟩:=extremo_normalizado_desde_una_sucesion kp k1 m1 lp
    (fun j=>eq _ (inside j)) (fun j=>sp _ (inside j))
    (fun j=>Real.toNNReal_pos.mpr (inside j).1)
    (fun j=>by rw [yr]; exact (inside j).2) (by simpa only [yr] using z)
  refine ⟨P₀,p₀,b₀,g₀,?_,?_⟩
  · intro x hx
    by_cases z : x=0
    · subst x; simpa [completarEnCero] using e₀
    · simpa [completarEnCero,z] using eq x ⟨lt_of_le_of_ne hx.1 (Ne.symm z),hx.2⟩
  · intro x hx
    by_cases z : x=0
    · subst x; simpa [completarEnCero] using sp₀
    · simpa [completarEnCero,z] using sp x ⟨lt_of_le_of_ne hx.1 (Ne.symm z),hx.2⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.extender_rama_desde_el_interior
