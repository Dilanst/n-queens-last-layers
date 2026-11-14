import ResidualDeLasFibrasTrasUnaTraslacion
import SeccionDeUnaDiagonal
import CavidadDeUnaFibraFisica
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set MeasureTheory Perfil
open scoped Interval
def familiaDeFranja : Fin 3→Fin 4 | 0=>1 | 1=>2 | 2=>3
def cargaDeFranja (u : ℝ×ℝ→ℝ) (i : Fin 3) (s : ℝ) :=
  ∫ r in (0:ℝ)..1,enLaFranja u i s r

theorem carga_de_franja_con_densidades_iguales {u v : ℝ×ℝ→ℝ}
    (h : ∀ r∈unidadCerrada,∀ c∈unidadCerrada,u (r,c)=v (r,c)) (i : Fin 3) (s : ℝ) :
    cargaDeFranja u i s=cargaDeFranja v i s := by
  apply intervalIntegral.integral_congr
  intro r hr; rw [uIcc_of_le zero_le_one] at hr
  dsimp only [enLaFranja]; split_ifs with hc
  · exact h r hr _ hc
  · rfl

theorem carga_nula_fuera_de_la_etiqueta (u : ℝ×ℝ→ℝ) (i : Fin 3) {s : ℝ}
    (fuera : s∉rangoF (familiaDeFranja i)) : cargaDeFranja u i s=0 := by
  have h : EqOn (enLaFranja u i s) (fun _=>0) (uIcc (0:ℝ) 1) := by
    intro r hr; rw [uIcc_of_le zero_le_one] at hr
    dsimp only [enLaFranja]; split_ifs with h
    · exfalso; apply fuera
      fin_cases i <;> norm_num [columnaEnFibra,familiaDeFranja,rangoF,extremoIzq,extremoDer,unidadCerrada] at h ⊢
      all_goals first | exact h | constructor <;> linarith [h.1,h.2,hr.1,hr.2]
    · rfl
  unfold cargaDeFranja; rw [intervalIntegral.integral_congr h]; simp

private theorem franja_oblicua (p : FactoresContinuos) (anti : Bool) {d : ℝ}
    (hd : d∈Icc (-1:ℝ) 1) :
    cargaDeFranja (fun z=>pesoContinuo p z.1 z.2) (if anti then 2 else 1) (if anti then d+1 else d)
      =integralDesplazada p d anti := by
  unfold cargaDeFranja
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  apply Eq.trans _ (integral_de_la_seccion p anti hd)
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  cases anti <;> simp only [Bool.false_eq_true,if_true,if_false,enLaFranja,columnaEnFibra,colOblicua]
  · have eq : r-d∈unidadCerrada ↔ d∈ventana r := by
      change (0≤r-d ∧ r-d≤1) ↔ r-1≤d ∧ d≤r
      constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp [eq]
  · have eq : d+1-r∈unidadCerrada ↔ d∈ventana r := by
      change (0≤d+1-r ∧ d+1-r≤1) ↔ r-1≤d ∧ d≤r
      constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
    simp [eq,show d+1-r=1-(r-d) by ring,show 1-(r-d)∈unidadCerrada ↔ d∈ventana r by
      simpa only [show 1-(r-d)=d+1-r by ring] using eq]

theorem carga_en_la_etiqueta_fisica (p : FactoresContinuos) (i : Fin 3) {s : ℝ}
    (hs : s∈rangoF (familiaDeFranja i)) :
    cargaDeFranja (fun z=>pesoContinuo p z.1 z.2) i s=integralFisica p (familiaDeFranja i) s := by
  fin_cases i
  · change s∈unidadCerrada at hs
    simp [cargaDeFranja,enLaFranja,columnaEnFibra,integralFisica,familiaDeFranja,hs]
  · exact franja_oblicua p false hs
  · have hd : s-1∈Icc (-1:ℝ) 1 := by
      change 0≤s ∧ s≤2 at hs; constructor <;> linarith [hs.1,hs.2]
    simpa [familiaDeFranja,integralFisica] using franja_oblicua p true hd

theorem carga_de_franja_por_escalar (b : ℝ) (u : ℝ×ℝ→ℝ) (i : Fin 3) (s : ℝ) :
    cargaDeFranja (fun z=>b*u z) i s=b*cargaDeFranja u i s := by
  unfold cargaDeFranja; rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr; intro r _
  simp only [enLaFranja]; split_ifs <;> simp
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.carga_de_franja_con_densidades_iguales
#print axioms ArticuloA.Historias.carga_nula_fuera_de_la_etiqueta
#print axioms ArticuloA.Historias.carga_en_la_etiqueta_fisica
#print axioms ArticuloA.Historias.carga_de_franja_por_escalar
