import ElevacionesDelCuadrado
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open Set MeasureTheory
open scoped BigOperators Interval NNReal ENNReal
namespace ArticuloA.Perfil
noncomputable section

def coord : Fin 4 → ℝ×ℝ → ℝ
  | 0,z => z.1
  | 1,z => z.2
  | 2,z => z.1-z.2
  | 3,z => z.1+z.2

def marginalRef : Fin 4 → Measure ℝ
  | 0 => volume.restrict (Ioc (0:ℝ) 1)
  | 1 => volume.restrict (Ioc (0:ℝ) 1)
  | 2 => volume.restrict (Ioc (-1:ℝ) 1)
  | 3 => volume.restrict (Ioc (0:ℝ) 2)

theorem coord_medible (i : Fin 4) : Measurable (coord i) := by
  fin_cases i
  exacts [measurable_fst,measurable_snd,measurable_fst.sub measurable_snd,measurable_fst.add measurable_snd]

structure LeyMarginal (ν : ℝ×ℝ→ℝ≥0) (m : Fin 4→ℝ→ℝ≥0) : Prop where
  densidad : Measurable ν
  densidadLinea : ∀ i,Measurable (m i)
  imagen : ∀ i,Measure.map (coord i) (cuadrado.withDensity (fun z => ν z))=
    (marginalRef i).withDensity (fun x => m i x)

theorem adjuncion {ν m} (ley : LeyMarginal ν m) (i : Fin 4) (g : ℝ→ℝ) (mg : Measurable g) :
    (∫ z,(ν z:ℝ)*g (coord i z) ∂cuadrado)=∫ x,(m i x:ℝ)*g x ∂marginalRef i := by
  have t := integral_map (μ:=cuadrado.withDensity (fun z => (ν z:ℝ≥0∞))) (coord_medible i).aemeasurable
    (f:=g) mg.aestronglyMeasurable
  rw [ley.imagen i,integral_withDensity_eq_integral_smul (ley.densidadLinea i),
    integral_withDensity_eq_integral_smul ley.densidad] at t
  exact t.symm

def masaDensidad (ν : ℝ×ℝ→ℝ≥0) : ℝ := ∫ z,(ν z:ℝ) ∂cuadrado
def xlogx (x : ℝ) := x*Real.log x
def valorEntropico (ν : ℝ×ℝ→ℝ≥0) (u : Fin 4→ℝ→ℝ) :=
  -3*masaDensidad ν-(∫ z,xlogx (ν z) ∂cuadrado)-
    ∑ i : Fin 4,∫ x,xlogx (u i x) ∂marginalRef i

theorem masa_de_cada_linea {ν m} (ley : LeyMarginal ν m) (i : Fin 4) :
    (∫ x,(m i x:ℝ) ∂marginalRef i)=masaDensidad ν := by
  simpa only [masaDensidad,mul_one] using (adjuncion ley i (fun _ => (1:ℝ)) measurable_const).symm

theorem complemento_integrado {ν m} (ley : LeyMarginal ν m) (u : Fin 4→ℝ→ℝ)
    (i : Fin 4) (g : ℝ→ℝ) (mg : Measurable g)
    (c : ∀ᵐ x ∂marginalRef i,(m i x:ℝ)+u i x=1)
    (i₁ : Integrable (fun x => (m i x:ℝ)*g x) (marginalRef i))
    (i₂ : Integrable (fun x => u i x*g x) (marginalRef i)) :
    (∫ z,(ν z:ℝ)*g (coord i z) ∂cuadrado)+(∫ x,u i x*g x ∂marginalRef i)=∫ x,g x ∂marginalRef i := by
  rw [adjuncion ley i g mg,←integral_add i₁ i₂]
  apply integral_congr_ae
  filter_upwards [c] with x hx
  rw [←add_mul,hx,one_mul]
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.adjuncion
#print axioms ArticuloA.Perfil.masa_de_cada_linea
#print axioms ArticuloA.Perfil.complemento_integrado
