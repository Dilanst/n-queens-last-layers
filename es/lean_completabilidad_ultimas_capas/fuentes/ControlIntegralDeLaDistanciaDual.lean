import DistanciaCuadraticaDePotenciales
import RepresentantesDeLaCajaDual
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def diferenciaDual {H : ℝ} (u v : CajaDual H) (i : Fin 4) (s : ℝ) := |campoDual u i s-campoDual v i s|

theorem diferencia_dual_medible {H : ℝ} (u v : CajaDual H) (i : Fin 4) : Measurable (diferenciaDual u v i) :=
  ((campo_dual_medible u i).sub (campo_dual_medible v i)).norm

theorem diferencia_dual_acotada {H : ℝ} (hp : 0≤H) (u v : CajaDual H) (i : Fin 4) (s : ℝ) :
    diferenciaDual u v i s≤H := by
  have a:=campo_dual_acotado hp u i s; have b:=campo_dual_acotado hp v i s
  exact abs_le.mpr ⟨by linarith [a.1,b.2],by linarith [a.2,b.1]⟩

theorem integrable_diferencia_dual {H : ℝ} (hp : 0≤H) (u v : CajaDual H) (i : Fin 4) :
    Integrable (diferenciaDual u v i) (marginalRef i) :=
  integral_acotada_dual (diferencia_dual_medible u v i) (fun s=>(abs_abs _).le.trans (diferencia_dual_acotada hp u v i s))

theorem integrable_cuadrado_dual {H : ℝ} (hp : 0≤H) (u v : CajaDual H) (i : Fin 4) :
    Integrable (fun s=>(campoDual u i s-campoDual v i s)^2) (marginalRef i) := by
  apply integral_acotada_dual (((campo_dual_medible u i).sub (campo_dual_medible v i)).pow_const 2) (M:=H^2)
  intro s; rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (diferencia_dual_acotada hp u v i s) _

theorem masa_de_etiqueta_a_lo_sumo_dos (i : Fin 4) : (marginalRef i).real univ≤2 := by
  fin_cases i <;> norm_num [marginalRef,Measure.real,Real.volume_Ioc]

theorem integral_diferencia_dual {H : ℝ} (hp : 0≤H) (u v : CajaDual H) (i : Fin 4) :
    (∫ s,diferenciaDual u v i s ∂marginalRef i)≤2*dist u v := by
  let D:=dist (u.val i) (v.val i)
  let μ:=marginalRef i
  let g:=diferenciaDual u v i
  have gi:=integrable_diferencia_dual hp u v i
  have g2 : Integrable (fun s=>g s^2) μ := by simpa [g,diferenciaDual,sq_abs] using integrable_cuadrado_dual hp u v i
  have val : (∫ s,g s^2 ∂μ)=D^2 := by
    simpa [g,diferenciaDual,sq_abs] using (distancia_L2_por_representantes (u.val i) (v.val i)
      (campo_dual_ae u i) (campo_dual_ae v i)).symm
  have ord s : 2*D*g s≤g s^2+D^2 := by nlinarith only [sq_nonneg (g s-D)]
  have comp:=integral_mono (gi.const_mul (2*D)) (g2.add (integrable_const (D^2))) ord
  change (∫ s,(2*D)*g s ∂μ)≤∫ s,g s^2+D^2 ∂μ at comp
  rw [integral_const_mul,integral_add g2 (integrable_const _),val,integral_const,smul_eq_mul] at comp
  have high := mul_le_mul_of_nonneg_right (masa_de_etiqueta_a_lo_sumo_dos i) (sq_nonneg D)
  have sub : D≤dist u v := dist_le_pi_dist u.val v.val i
  by_cases p : D=0
  · have eq : u.val i=v.val i := dist_eq_zero.mp p
    have ae := (campo_dual_ae u i).trans (eq ▸ (campo_dual_ae v i).symm)
    have zero : g=ᵐ[μ] 0 := ae.mono (fun s hs=>by simp [g,diferenciaDual,hs])
    rw [show (∫ s,diferenciaDual u v i s ∂marginalRef i)=0 by simpa using integral_congr_ae zero]
    positivity
  · have dp : 0<D := (dist_nonneg : 0≤D).lt_of_ne' p
    have l : (∫ s,g s ∂μ)≤2*D := by
      by_contra! hh
      have strict:=mul_lt_mul_of_pos_left hh dp
      change 2*D*(∫ s,g s ∂μ)≤D^2+(marginalRef i).real univ*D^2 at comp
      nlinarith only [strict,comp,high,sq_nonneg D]
    exact l.trans (by linarith)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.diferencia_dual_medible
#print axioms ArticuloA.Historias.diferencia_dual_acotada
#print axioms ArticuloA.Historias.integrable_diferencia_dual
#print axioms ArticuloA.Historias.integrable_cuadrado_dual
#print axioms ArticuloA.Historias.masa_de_etiqueta_a_lo_sumo_dos
#print axioms ArticuloA.Historias.integral_diferencia_dual
