import LasCuatroFamiliasDeMasasRetenidas
import BalanceFisicoCompleto
namespace ArticuloA.Historias
open Repair Perfil Trayectoria Trayectoria.E2
open scoped BigOperators
noncomputable section
open Classical

def familiaDeReserva {n} : FibraDeB1 n → Fin 4
  | .inl (false,_) => 0
  | .inl (true,_) => 1
  | .inr (false,_) => 2
  | .inr (true,_) => 3

theorem misma_fibra_que_su_representante {n} (i : FibraDeB1 n) (z : Cell n)
    (hz : enLaFibra i z) (e : Cell n) :
    enLaFibra i e ↔ lines e (familiaDeReserva i)=lines z (familiaDeReserva i) := by
  have zcol:=z.2.isLt
  have ecol:=e.2.isLt
  rcases i with ⟨b,j⟩|⟨b,j⟩ <;> cases b <;>
    simp [enLaFibra,familiaDeReserva,etiquetaD,etiquetaA,lines,Fin.ext_iff] at hz ⊢ <;> omega

theorem carga_sobre_una_fibra_fisica {n} (q : ℕ) (p : FactoresContinuos)
    (i : FibraDeB1 n) (z : Cell n) (hz : enLaFibra i z) :
    masaBajo (cargaCelda n q p) (enLaFibra i)=
      cargaLinea n q p (familiaDeReserva i) ⟨_,rango z (familiaDeReserva i)⟩ := by
  unfold masaBajo cargaLinea gradoInicial
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : enLaFibra i e
  · simp [pesoCuando,cargaCelda,h,(misma_fibra_que_su_representante i z hz e).mp h]
  · have ne:=mt (misma_fibra_que_su_representante i z hz e).mpr h
    simp [pesoCuando,h,ne]

theorem masa_nula_de_fibra_vacia {n} (w : Cell n→ℝ) (i : FibraDeB1 n)
    (empty : ¬ ∃ z,enLaFibra i z) : masaBajo w (enLaFibra i)=0 := by
  apply Finset.sum_eq_zero
  intro e _
  simp [pesoCuando,show ¬enLaFibra i e from fun h=>empty ⟨e,h⟩]

theorem masa_y_signo_de_la_densidad_fisica {n q : ℕ} {p κ M L}
    (hn : 0<n) (data : ControlEspacial p κ M L) (kp : 0<κ) :
    (∑ e : Cell n,cargaCelda n q p e)=(q:ℝ) ∧ ∀ e,0≤cargaCelda n q p e := by
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have wp : 0<Wfisico n p:=(mul_pos (pow_pos kp _) (pow_pos np 2)).trans_le (masa_inferior data kp.le)
  constructor
  · simp only [cargaCelda,←Finset.sum_div,←Finset.mul_sum]
    change (q:ℝ)*Wfisico n p/Wfisico n p=q
    field_simp
  · intro e
    have pos:0≤pesoFisico n p e:=(pow_nonneg kp.le 4).trans ((limites_del_producto data kp.le _ _
      (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)).1)
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) pos) wp.le
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.carga_sobre_una_fibra_fisica
#print axioms ArticuloA.Historias.masa_y_signo_de_la_densidad_fisica
