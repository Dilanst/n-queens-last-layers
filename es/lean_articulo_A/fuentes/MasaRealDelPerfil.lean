import CuadraturaDelTablero
import IndicesFisicosDelPerfil
import ProductoDeCuatroFactores
open MeasureTheory Set
open scoped BigOperators Interval NNReal
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

theorem cuadratura_de_Wreal (n : ℕ) (hn : 0<n) (x : ℝ≥0) (p : FactoresContinuos) (L : ℝ) (lp : 0≤L)
    (rLip : ∀ r∈unidadCerrada,∀ i∈unidadCerrada,∀ c∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p i c|≤L*|r-i|)
    (cLip : ∀ r∈unidadCerrada,∀ c∈unidadCerrada,∀ j∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p r j|≤L*|c-j|) :
    |Wreal n (sameColors (pesosMalla n x p))-(x:ℝ)^2*(n:ℝ)^2*integralTablero (pesoContinuo p)|≤
      (x:ℝ)^2*(2*L*n) := by
  have e := cuadratura_dos_dimensiones n hn (pesoContinuo p) L lp rLip cLip
  rw [Wreal_malla,mul_assoc,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _),abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (by simpa only [centro,nodo,zero_add,medio,muestraTablero] using e) (sq_nonneg _)

theorem log_Wreal_del_perfil (n q : ℕ) (hn : 0<n) (hq : 0<q) (qn : q≤n) (x : ℝ≥0) (xp : 0<x)
    (p : FactoresContinuos) (L b m₀ : ℝ) (lp : 0≤L) (bp : 0<b) (mp : 0<m₀)
    (low : m₀ ≤ integralTablero (pesoContinuo p))
    (mass : integralTablero (pesoContinuo p)=(q:ℝ)/(n*b))
    (positive : 0<Wreal n (sameColors (pesosMalla n x p)))
    (rLip : ∀ r∈unidadCerrada,∀ i∈unidadCerrada,∀ c∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p i c|≤L*|r-i|)
    (cLip : ∀ r∈unidadCerrada,∀ c∈unidadCerrada,∀ j∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p r j|≤L*|c-j|) :
    (q:ℝ)*(Real.log (Wreal n (sameColors (pesosMalla n x p)))-(Real.log n+Real.log q-Real.log (b/(x:ℝ)^2)))≤2*L/m₀ := by
  let S := muestraTablero n (pesoContinuo p)
  have eq : Wreal n (sameColors (pesosMalla n x p))=(x:ℝ)^2*S := by
    simpa only [S,muestraTablero,centro,nodo,zero_add,medio] using Wreal_malla n x p
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  rw [eq] at positive ⊢
  have spos : 0<S := pos_of_mul_pos_right positive (sq_nonneg _)
  have err := cuadratura_dos_dimensiones n hn (pesoContinuo p) L lp rLip cLip
  rw [abs_sub_comm] at err
  exact error_de_masa_real n q hn hq qn x b _ m₀ S (2*L) xr bp mp (by positivity) low spos mass (abs_le.mp err).2

theorem log_Wreal_del_lleno (n : ℕ) (hn : 0<n) (p : FactoresContinuos) (L b m₀ : ℝ)
    (lp : 0≤L) (bp : 0<b) (mp : 0<m₀) (low : m₀ ≤ integralTablero (pesoContinuo p))
    (mass : integralTablero (pesoContinuo p)=1/b) (positive : 0<Wreal n (coloresLlenos n (pesosMalla n 1 p)))
    (rLip : ∀ r∈unidadCerrada,∀ i∈unidadCerrada,∀ c∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p i c|≤L*|r-i|)
    (cLip : ∀ r∈unidadCerrada,∀ c∈unidadCerrada,∀ j∈unidadCerrada,|pesoContinuo p r c-pesoContinuo p r j|≤L*|c-j|) :
    (n:ℝ)*(Real.log (Wreal n (coloresLlenos n (pesosMalla n 1 p)))-(Real.log n+Real.log n-Real.log b))≤2*L/m₀ := by
  rw [Wreal_lleno_malla] at positive ⊢
  have np : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have m : integralTablero (pesoContinuo p)=(n:ℝ)/(n*b) := by rw [mass]; field_simp
  simpa using log_Wreal_del_perfil n n hn hn le_rfl 1 zero_lt_one p L b m₀ lp bp mp low m positive rLip cLip
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.log_Wreal_del_perfil
#print axioms ArticuloA.Historias.log_Wreal_del_lleno
