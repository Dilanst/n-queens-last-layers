import ContinuidadDeLasCuatroFibras
open Set Filter MeasureTheory
open scoped Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

/-- Column at row r in the fiber with offset d. For an antidiagonal,
the physical coordinate of the line is d+1. -/
def colOblicua (anti : Bool) (r d : ℝ) := if anti then 1-(r-d) else r-d

theorem recorte_de_intervalos {a b u v : ℝ} (h : a≤b) (ok : Icc a b ⊆ Icc u v) (F : ℝ→ℝ) :
    (∫ t in Icc u v, (Icc a b).indicator F t) = ∫ t in a..b,F t := by
  rw [integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr ok,intervalIntegral.integral_of_le h,integral_Icc_eq_integral_Ioc]

def ventana (r : ℝ) : Set ℝ := Icc (r-1) r
def inicioFibra (d : ℝ) := max d 0
def finFibra (d : ℝ) := 1-|d|+inicioFibra d

theorem pertenencia_de_la_seccion {r d : ℝ} (hr : r∈Icc 0 1) :
    d∈ventana r ↔ r∈Icc (inicioFibra d) (finFibra d) := by
  dsimp [ventana,inicioFibra,finFibra,mem_Icc] at *
  by_cases h : 0≤d
  · rw [abs_of_nonneg h,max_eq_left h]; constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith [hr.1,hr.2]
  · have z:=le_of_not_ge h
    rw [abs_of_nonpos z,max_eq_right z]; constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith [hr.1,hr.2]

theorem extremos_de_la_seccion {d : ℝ} (hd : d∈Icc (-1) 1) :
    inicioFibra d≤finFibra d ∧ Icc (inicioFibra d) (finFibra d)⊆Icc 0 1 := by
  have z:=abs_le.mpr hd
  dsimp [inicioFibra,finFibra]
  refine ⟨by linarith,?_⟩
  intro t ht
  refine ⟨(le_max_right _ _).trans ht.1,ht.2.trans ?_⟩
  have w : max d 0≤|d| := max_le (le_abs_self _) (abs_nonneg _)
  linarith

theorem integral_de_la_seccion (p : FactoresContinuos) (anti : Bool) {d : ℝ} (hd : d∈Icc (-1) 1) :
    (∫ r in Icc (0:ℝ) 1,if d∈ventana r then pesoContinuo p r (colOblicua anti r d) else 0)
      =integralDesplazada p d anti := by
  let f:=fun r => pesoContinuo p r (colOblicua anti r d)
  obtain ⟨le,sub⟩:=extremos_de_la_seccion hd
  calc _ = ∫ r in Icc (0:ℝ) 1,(Icc (inicioFibra d) (finFibra d)).indicator f r := by
             apply setIntegral_congr_fun measurableSet_Icc; intro r hr
             simp only [Set.indicator,pertenencia_de_la_seccion hr,f]
       _ = ∫ r in inicioFibra d..finFibra d,f r := recorte_de_intervalos le sub f
       _ = ∫ t in (0:ℝ)..1-|d|,f (inicioFibra d+t) := by
             rw [intervalIntegral.integral_comp_add_left]; simp [finFibra,add_comm]
       _ = _ := by
             apply intervalIntegral.integral_congr; intro t _
             have c : inicioFibra d + t-d=max (-d) 0+t := by
               by_cases pos : 0≤d
               · simp [inicioFibra,max_eq_left pos,max_eq_right (neg_nonpos.mpr pos)]
               · have neg:=le_of_not_ge pos
                 simp [inicioFibra,max_eq_right neg,max_eq_left (neg_nonneg.mpr neg)]; ring
             dsimp only [f,colOblicua]; rw [c]; rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.integral_de_la_seccion
