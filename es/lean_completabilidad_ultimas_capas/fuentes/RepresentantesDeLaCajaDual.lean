import CajaCompletaDeLosCuatroPotenciales
import ConjuntosNulosDeLasCuatroEtiquetas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
abbrev CajaDual (H : ℝ) := ↥(cajaDePotenciales H)

def campoDual {H : ℝ} (u : CajaDual H) (i : Fin 4) (s : ℝ) := min (max (u.val i s) 0) H

theorem campo_dual_acotado {H : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4) (s : ℝ) :
    campoDual u i s∈Icc 0 H := ⟨le_min (le_max_right _ _) hp,min_le_right _ _⟩

theorem campo_dual_medible {H : ℝ} (u : CajaDual H) (i : Fin 4) : Measurable (campoDual u i) :=
  ((Lp.stronglyMeasurable (u.val i)).measurable.max measurable_const).min measurable_const

theorem campo_dual_ae {H : ℝ} (u : CajaDual H) (i : Fin 4) : campoDual u i=ᵐ[marginalRef i] u.val i := by
  filter_upwards [u.property i] with s hs
  exact (min_eq_left (by simpa [max_eq_left hs.1] using hs.2 : max (u.val i s) 0≤H)).trans (max_eq_left hs.1)

def sumaDual {H : ℝ} (u : CajaDual H) (z : ℝ×ℝ) := ∑ i : Fin 4,campoDual u i (coord i z)
def particionDual {H : ℝ} (u : CajaDual H) := ∫ z,exp (-sumaDual u z) ∂cuadrado
def costoDual {H : ℝ} (u : CajaDual H) (i : Fin 4) := ∫ s,potencialDeHolgura (campoDual u i s) ∂marginalRef i
def funcionalDual {H : ℝ} (d : ℝ) (u : CajaDual H) := (∑ i : Fin 4,costoDual u i)+d*log (particionDual u)

theorem suma_dual_medible {H : ℝ} (u : CajaDual H) : Measurable (sumaDual u) :=
  Finset.measurable_sum _ (fun i _=>(campo_dual_medible u i).comp (coord_medible i))

theorem suma_dual_acotada {H : ℝ} (hp : 0≤H) (u : CajaDual H) (z : ℝ×ℝ) :
    sumaDual u z∈Icc 0 (4*H) := by
  refine ⟨Finset.sum_nonneg (fun i _=>(campo_dual_acotado hp u i _).1),?_⟩
  exact (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 4)))=>(campo_dual_acotado hp u i (coord i z)).2)).trans_eq (by simp)

theorem integral_acotada_dual {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α→ℝ} (fm : Measurable f) {M : ℝ} (bound : ∀ s,|f s|≤M) : Integrable f μ :=
  (integrable_const M).mono' fm.aestronglyMeasurable (Eventually.of_forall bound)

local instance : IsProbabilityMeasure unidad:=⟨by simp [unidad,Real.volume_Icc]⟩
local instance : IsProbabilityMeasure cuadrado:=by unfold cuadrado; infer_instance

theorem densidad_dual_integrable {H : ℝ} (hp : 0≤H) (u : CajaDual H) :
    Integrable (fun z=>exp (-sumaDual u z)) cuadrado := by
  apply integral_acotada_dual ((suma_dual_medible u).neg.exp) (M:=1)
  intro z; rw [abs_of_pos (exp_pos _)]; exact exp_le_one_iff.mpr (neg_nonpos.mpr (suma_dual_acotada hp u z).1)

theorem particion_dual_acotada {H : ℝ} (hp : 0≤H) (u : CajaDual H) :
    particionDual u∈Icc (exp (-(4*H))) 1 := by
  have lo:=integral_mono (integrable_const (μ:=cuadrado) (exp (-(4*H)))) (densidad_dual_integrable hp u)
    (fun z=>exp_le_exp.mpr (neg_le_neg (suma_dual_acotada hp u z).2))
  have hi:=integral_mono (densidad_dual_integrable hp u) (integrable_const (μ:=cuadrado) (1:ℝ))
    (fun z=>exp_le_one_iff.mpr (neg_nonpos.mpr (suma_dual_acotada hp u z).1))
  simpa [particionDual,integral_const] using And.intro lo hi

theorem costo_dual_integrable {H : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4) :
    Integrable (fun s=>potencialDeHolgura (campoDual u i s)) (marginalRef i) := by
  have m:=campo_dual_medible u i
  apply integral_acotada_dual ((m.add m.neg.exp).sub measurable_const) (M:=H)
  intro s
  have hs:=campo_dual_acotado hp u i s
  have p:=add_one_le_exp (-campoDual u i s)
  have top:=exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)
  exact abs_le.mpr ⟨by linarith,by linarith [hs.2]⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.campo_dual_acotado
#print axioms ArticuloA.Historias.campo_dual_medible
#print axioms ArticuloA.Historias.campo_dual_ae
#print axioms ArticuloA.Historias.suma_dual_medible
#print axioms ArticuloA.Historias.suma_dual_acotada
#print axioms ArticuloA.Historias.densidad_dual_integrable
#print axioms ArticuloA.Historias.particion_dual_acotada
#print axioms ArticuloA.Historias.costo_dual_integrable
