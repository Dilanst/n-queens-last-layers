import MasasDelOptimoEnLosIntervalos
import ContinuidadDelValorEnElLleno
open Set MeasureTheory Filter
open scoped BigOperators NNReal Interval Topology
namespace ArticuloA.Historias
open Perfil
noncomputable section

def areaCentrada (f : ℝ→ℝ→ℝ) := ∫ r in (-(1/2:ℝ))..(1/2),∫ c in (-(1/2:ℝ))..(1/2),f r c
def intervaloCentrado (f : ℝ→ℝ) := ∫ t in (-1:ℝ)..1,f t
def costoOblicuo (u : ℝ) := u*Real.log (2*u)
def valorCentrado (P : TableroMedido) := -3+2*Real.log 2-
  areaCentrada (fun r c => xlogx (P.ν (r+1/2,c+1/2)))-
  intervaloCentrado (fun d => costoOblicuo (P.u 2 d))-
  intervaloCentrado (fun d => costoOblicuo (P.u 3 (d+1)))

theorem cambio_centrado_de_coordenadas (r c : ℝ) :
    (r-1/2)-(c-1/2)=r-c ∧ (r-1/2)+(c-1/2)=r+c-1 := by constructor <;> ring

theorem trasladar_area (f : ℝ→ℝ→ℝ) :
    areaCentrada (fun r c => f (r+1/2) (c+1/2))=integralTablero f := by
  unfold areaCentrada integralTablero integralFila
  have tr (g : ℝ→ℝ) : (∫ r in (-(1/2:ℝ))..(1/2),g (r+1/2))=∫ t in (0:ℝ)..1,g t := by
    rw [intervalIntegral.integral_comp_add_right]; norm_num
  simp_rw [tr]
  exact tr (fun r => ∫ c in (0:ℝ)..1,f r c)

theorem constantes_de_vacancia (u : ℝ) : costoOblicuo u=xlogx u+u*Real.log 2 := by
  by_cases z : u=0
  · simp [z,costoOblicuo,xlogx]
  · rw [costoOblicuo,Real.log_mul (by norm_num) z]; unfold xlogx; ring

theorem costo_de_una_linea {P p b κ M L} (h : EulerFisica P p 0 b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (lp : 0≤L) (i : Fin 4) (ob : 2 ≤ i.val) :
    (∫ t,costoOblicuo (P.u i t) ∂marginalRef i)=(∫ t,xlogx (P.u i t) ∂marginalRef i)+Real.log 2 := by
  have full : P.rho=1 := by simpa using h.masa
  have mass : (∫ t,P.u i t ∂marginalRef i)=1 := by
    unfold TableroMedido.u
    rw [integral_sub (integrable_const _) (P.m_integrable i),medida_linea_oblicua i ob,masa_de_cada_linea P.ley i]
    change 2-P.rho=1; rw [full]; norm_num
  simp_rw [constantes_de_vacancia]
  rw [integral_add ((entropias_del_optimo_integrables h sp kp lp).2 i) ((P.u_integrable i).mul_const _),
    integral_mul_const,mass,one_mul]

theorem vacancia_transversal_llena {P p b} (h : EulerFisica P p 0 b) (i : Fin 4) (rc : i.val<2) :
    ∀ᵐ t ∂marginalRef i,P.u i t=0 := (h.linea i).mono (fun _ e => by simpa [holguraLinea,rc] using e)

theorem normalizacion_de_simkin {P p b κ M L} (h : EulerFisica P p 0 b) (sp : ControlEspacial p κ M L)
    (kp : 0<κ) (lp : 0≤L) : valorCentrado P=P.s := by
  have full : P.rho=1 := by simpa using h.masa
  have area := integral_de_area_igual_a_iterada (fun r c => xlogx (P.ν (r,c)))
    (entropias_del_optimo_integrables h sp kp lp).1
  have empty (i : Fin 4) (rc : i.val<2) : (∫ t,xlogx (P.u i t) ∂marginalRef i)=0 := by
    apply integral_eq_zero_of_ae
    exact (vacancia_transversal_llena h i rc).mono (fun _ z => by simp [z,xlogx])
  have d : intervaloCentrado (fun t => costoOblicuo (P.u 2 t))=∫ t,costoOblicuo (P.u 2 t) ∂marginalRef 2 :=
    intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)
  have a : intervaloCentrado (fun t => costoOblicuo (P.u 3 (t+1)))=∫ t,costoOblicuo (P.u 3 t) ∂marginalRef 3 := by
    unfold intervaloCentrado
    rw [intervalIntegral.integral_comp_add_right (f:=fun t => costoOblicuo (P.u 3 t)) 1]
    norm_num
    exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤2)
  unfold valorCentrado TableroMedido.s valorEntropico
  rw [trasladar_area (fun r c => xlogx (P.ν (r,c))),←area,d,a,costo_de_una_linea h sp kp lp 2 (by decide),
    costo_de_una_linea h sp kp lp 3 (by decide),Fin.sum_univ_four,empty 0 (by decide),empty 1 (by decide)]
  change _ = -3*P.rho-_-_
  rw [full]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.normalizacion_de_simkin
