import AdjuncionDeLasCuatroMarginales
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MeasureTheory Set Filter
open scoped BigOperators NNReal
namespace ArticuloA.Perfil
noncomputable section

structure TableroMedido where
  ν : ℝ×ℝ→ℝ≥0
  m : Fin 4→ℝ→ℝ≥0
  ley : LeyMarginal ν m
  masaFinita : Integrable (fun z => (ν z:ℝ)) cuadrado
  admisible : ∀ i,∀ᵐ x ∂marginalRef i,(m i x:ℝ)≤1

def TableroMedido.u (P : TableroMedido) (i : Fin 4) (y : ℝ) := 1-(P.m i y:ℝ)
def TableroMedido.s (P : TableroMedido) := valorEntropico P.ν P.u
def TableroMedido.rho (P : TableroMedido) := masaDensidad P.ν

structure CampoIntegrable (P : TableroMedido) (v : Fin 4→ℝ→ℝ) : Prop where
  medible : ∀ i,Measurable (v i)
  ocupada : ∀ i,Integrable (fun z => (P.ν z:ℝ)*v i (coord i z)) cuadrado
  marginal : ∀ i,Integrable (fun x => (P.m i x:ℝ)*v i x) (marginalRef i)
  libre : ∀ i,Integrable (fun x => P.u i x*v i x) (marginalRef i)

theorem complementar_campo (P : TableroMedido) {v} (h : CampoIntegrable P v) :
    (∑ i : Fin 4,∫ z,(P.ν z:ℝ)*v i (coord i z) ∂cuadrado)+
    (∑ i : Fin 4,∫ x,P.u i x*v i x ∂marginalRef i)=∑ i : Fin 4,∫ x,v i x ∂marginalRef i := by
  rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl
  intro i _
  exact complemento_integrado P.ley P.u i (v i) (h.medible i)
    (Eventually.of_forall (fun _ => by simp [TableroMedido.u])) (h.marginal i) (h.libre i)

theorem integrar_campo_del_tablero (P : TableroMedido) {v} (h : CampoIntegrable P v) (l : ℝ) :
    (∫ z,(P.ν z:ℝ)*(l+∑ i : Fin 4,v i (coord i z)) ∂cuadrado)=
    P.rho*l+∑ i : Fin 4,∫ z,(P.ν z:ℝ)*v i (coord i z) ∂cuadrado := by
  simp_rw [mul_add,Finset.mul_sum]
  rw [integral_add (P.masaFinita.mul_const l) (integrable_finset_sum _ (fun i _ => h.ocupada i)),
    integral_mul_const,integral_finset_sum _ (fun i _ => h.ocupada i)]
  rfl

theorem valor_de_euler (P : TableroMedido) {v} (hv : CampoIntegrable P v) (l : ℝ)
    (dens : ∀ᵐ z ∂cuadrado,Real.log (P.ν z)=l+∑ i : Fin 4,v i (coord i z))
    (vac : ∀ i,∀ᵐ x ∂marginalRef i,xlogx (P.u i x)=P.u i x*v i x) :
    P.s=P.rho*(-l-3)-∑ i : Fin 4,∫ x,v i x ∂marginalRef i := by
  have z : (∫ t,xlogx (P.ν t) ∂cuadrado)=P.rho*l+∑ i : Fin 4,∫ t,(P.ν t:ℝ)*v i (coord i t) ∂cuadrado := by
    rw [←integrar_campo_del_tablero P hv l]
    apply integral_congr_ae
    filter_upwards [dens] with t eq
    simp only [xlogx,eq]
  have vv : (∑ i : Fin 4,∫ x,xlogx (P.u i x) ∂marginalRef i)=
    ∑ i : Fin 4,∫ x,P.u i x*v i x ∂marginalRef i :=
    Finset.sum_congr rfl (fun i _ => integral_congr_ae (vac i))
  change -3*P.rho-_-_=_; rw [z,vv,←complementar_campo P hv]; ring

theorem log_del_producto {z b : ℝ} {y : Fin 4→ℝ} (bp : 0<b) (p : ∀ i,0<y i)
    (eq : z=b*y 0*y 1*y 2*y 3) : Real.log z=Real.log b+∑ i : Fin 4,Real.log (y i) := by
  rw [eq,Fin.sum_univ_four]
  have h0:=p 0; have h1:=p 1; have h2:=p 2; have h3:=p 3
  rw [Real.log_mul (mul_pos (mul_pos (mul_pos bp h0) h1) h2).ne' h3.ne',
    Real.log_mul (mul_pos (mul_pos bp h0) h1).ne' h2.ne',
    Real.log_mul (mul_pos bp h0).ne' h1.ne',Real.log_mul bp.ne' h0.ne']
  ring
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.valor_de_euler
#print axioms ArticuloA.Perfil.log_del_producto
