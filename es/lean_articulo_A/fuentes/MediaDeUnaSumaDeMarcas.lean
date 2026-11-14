import DieciseisPatronesEnUnMismoAtomo
import PasoOriginal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
variable {ι κ : Type}

theorem media_de_suma_finita (row : Atoms ℝ≥0 ι) (s : Finset κ) (f : κ→ι→ℝ) :
    media row (fun x => ∑ j∈s,f j x)=∑ j∈s,media row (f j) := by
  induction row with
  | nil => simp [media]
  | cons a xs ih =>
    simp only [media,ih,Finset.mul_sum,Finset.sum_add_distrib]

theorem media_con_constante (row : Atoms ℝ≥0 ι) (one : total masas row=1) (f : ι→ℝ) (v c : ℝ) :
    media row (fun i => c*f i+v)=c*media row f+v := by
  have r:=media_affine row f v c
  rw [one] at r
  change media row (fun x => v+c*f x)=1*v+c*media row f at r
  simpa only [add_comm,one_mul] using r

theorem media_de_diferencias (row : Atoms ℝ≥0 ι) (f g : ι→ℝ) :
    media row (fun i => f i-g i)=media row f-media row g := by
  induction row with
  | nil => simp [media]
  | cons a xs ih => simp only [media,ih]; ring

theorem promedio_de_un_resto (row : Atoms ℝ≥0 ι) (one : total masas row=1) (f : ι→ℝ) (B : ℝ)
    (bound : ∀ i∈row,|f i.2|≤B) : |media row f|≤B := by
  have const (b : ℝ) : media row (fun _ => b)=b := by
    simpa using media_con_constante row one (fun _ => (0:ℝ)) b 0
  apply abs_le.mpr
  constructor
  · rw [←const (-B)]
    exact media_mono row _ _ (fun i hi => (abs_le.mp (bound i hi)).1)
  · rw [←const B]
    exact media_mono row _ _ (fun i hi => (abs_le.mp (bound i hi)).2)

theorem media_de_una_marca (row : Atoms ℝ≥0 ι) (P : ι→Prop) :
    media row (fun x => estadoEscalar (P x))=(↑(meanN masas row (fun x => indicator (P x))):ℝ) := by
  rw [mean_indicator_avg]
  refine Eq.trans ?_ (media_coe row (mark masas P))
  congr 1
  funext x
  by_cases hx:P x <;> simp [estadoEscalar,indicator,mark,masas,hx]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_de_suma_finita
#print axioms ArticuloA.Historias.media_con_constante
#print axioms ArticuloA.Historias.media_de_diferencias
#print axioms ArticuloA.Historias.promedio_de_un_resto
#print axioms ArticuloA.Historias.media_de_una_marca
