import LeyCentradaDelPerfilLleno
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace ArticuloA.Historias
open Perfil
noncomputable section

/-- Full centered probability with the four projection constraints. The two coordinate laws
also imply support on the closed centered square up to null sets. -/
structure AdmisibleCentrada (μ : Measure (ℝ×ℝ)) : Prop where
  masa : μ univ=1
  transversales : ∀ i : Fin 4,i.val<2 → μ.map (coord i)=refCentrada i
  oblicuas : ∀ (i : Fin 4), (2 : ℕ) ≤ i.val → μ.map (coord i)≤refCentrada i

theorem admisibilidad_del_lleno {P p b} (h : EulerFisica P p 0 b) : AdmisibleCentrada (leyCentrada P) :=
  ⟨masa_centrada_uno h,filas_y_columnas_uniformes h,fun i _ => dominacion_de_las_oblicuas P i⟩

/-- External lower counting input in neighborhoods of the specified centered profile.
The neighborhood count is bounded by the full count. Its radius and start size may depend
on the tolerance. Only the lower estimate is used. -/
def ConteoLocalInferior (s : ℝ) := ∀ ε : ℝ,0<ε → ∃ vecinos : ℕ→ℕ,
  (∀ n,vecinos n≤count n n) ∧ ∀ᶠ n : ℕ in atTop,
    Real.exp ((n:ℝ)*Real.log n+(n:ℝ)*s-(n:ℝ)*ε)≤vecinos n

theorem conteo_local_implica_primer_orden {s : ℝ} (input : ConteoLocalInferior s) : CotaDePrimerOrden s := by
  intro ε ep
  obtain ⟨N,cap,lower⟩:=input ε ep
  filter_upwards [lower] with n hn
  have bound : Real.exp ((n:ℝ)*Real.log n+(n:ℝ)*s-(n:ℝ)*ε)≤count n n :=
    hn.trans (by exact_mod_cast cap n)
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) bound

theorem L1_con_entrada_de_conteo_centrada {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (K : ℕ)
    (cb : ContinuousWithinAt b (Icc 0 (1/2:ℝ)) 0)
    (fc : ∀ i,∀ t∈rangoF i,ContinuousWithinAt (fun x : ℝ => (factorF (p x) i t:ℝ)) (Icc 0 (1/2:ℝ)) 0)
    (externo : AdmisibleCentrada (leyCentrada (P 0)) → ConteoLocalInferior (valorCentrado (P 0))) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p ((h:ℝ)/n))) (d n) := by
  have hz : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have eq : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using rama.euler 0 hz
  have localcount:=externo (admisibilidad_del_lleno eq)
  rw [normalizacion_de_simkin eq (rama.espacio 0 hz) rama.kp rama.lp] at localcount
  exact L1_del_perfil_y_del_primer_orden rama K cb fc (conteo_local_implica_primer_orden localcount)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.L1_con_entrada_de_conteo_centrada
