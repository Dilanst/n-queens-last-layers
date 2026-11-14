import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RepresentanteFisicoDeLosCuatroLimites
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Real
def perdidaDelCoseno (s : ℝ) : ℝ := 1-cos (2*π*s)

theorem coseno_no_negativo_en_el_cuarto {s : ℝ} (sl : 0≤s) (sr : s≤1/4) : 0≤cos (2*π*s) := by
  apply cos_nonneg_of_mem_Icc
  constructor
  · linarith [mul_nonneg pi_pos.le sl,pi_pos]
  · nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr sr)]

theorem perdida_al_duplicar {s : ℝ} (sl : 0≤s) (sr : s≤1/4) :
    2*perdidaDelCoseno s≤perdidaDelCoseno (2*s) := by
  unfold perdidaDelCoseno
  rw [show 2*π*(2*s)=2*(2*π*s) by ring, cos_two_mul]
  nlinarith [mul_nonneg (coseno_no_negativo_en_el_cuarto sl sr) (sub_nonneg.mpr (cos_le_one (2*π*s)))]

theorem perdida_de_angulo_diadico {s : ℝ} (sl : 0≤s) (j : ℕ)
    (hr : (2:ℝ)^j*s≤1/4) : (2:ℝ)^j*perdidaDelCoseno s ≤ perdidaDelCoseno ((2:ℝ)^j*s) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have non : 0≤(2:ℝ)^j*s := mul_nonneg (by positivity) sl
    rw [pow_succ, mul_right_comm _ 2 s] at hr
    have h : (2:ℝ)^j*s≤1/4 := by linarith
    calc
      (2:ℝ)^(j+1)*perdidaDelCoseno s = 2*((2:ℝ)^j*perdidaDelCoseno s) := by rw [pow_succ]; ring
      _ ≤ 2*perdidaDelCoseno ((2:ℝ)^j*s) := by linarith only [ih h]
      _ ≤ perdidaDelCoseno (2*((2:ℝ)^j*s)) := perdida_al_duplicar non h
      _ = _ := by rw [pow_succ]; ring_nf

theorem perdida_menor_que_ocho_por_el_desplazamiento {s : ℝ} (sl : 0≤s) (sr : s≤1/4) :
    1-cos (2*π*s)≤8*s := by
  rcases eq_or_lt_of_le sl with rfl|sp
  · simp
  have den : 0<4*s := by positivity
  have large : 1≤1/(4*s) := (le_div_iff₀ den).mpr (by linarith)
  obtain ⟨j,left,right⟩:=exists_nat_pow_near large (show (1:ℝ)<2 by norm_num)
  have low := (le_div_iff₀ den).mp left
  have high := (div_lt_iff₀ den).mp right
  rw [pow_succ] at high
  have endp : (2:ℝ)^j*s≤1/4 := by linarith only [low]
  have non : 0≤(2:ℝ)^j*s := mul_nonneg (by positivity) sl
  have d:=perdida_de_angulo_diadico sl j endp
  have cap:=coseno_no_negativo_en_el_cuarto non endp
  unfold perdidaDelCoseno at d
  apply (le_of_mul_le_mul_left ?_ (by positivity : 0<(2:ℝ)^j))
  calc
    (2:ℝ)^j*(1-cos (2*π*s)) ≤ 1 := by linarith only [d,cap]
    _ ≤ (2:ℝ)^j*(8*s) := by linarith only [high]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.coseno_no_negativo_en_el_cuarto
#print axioms ArticuloA.Historias.perdida_al_duplicar
#print axioms ArticuloA.Historias.perdida_de_angulo_diadico
#print axioms ArticuloA.Historias.perdida_menor_que_ocho_por_el_desplazamiento
