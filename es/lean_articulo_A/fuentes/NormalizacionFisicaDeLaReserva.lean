import LasCuatroFamiliasDeMasasRetenidas
import NormalizadorComunDeLasFibrasDeB1
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

def pesoRetenido {n} (w : Cell n→ℝ) (u : LineaReservable n→Bool) (e : Cell n) : ℝ :=
  if quedaTrasReserva u e then w e else 0

theorem masa_de_fila_o_columna_es_auxiliar {n} (w : Cell n→ℝ) (u : LineaReservable n→Bool)
    (b : Bool) (r : Fin n) : masaBajo (pesoRetenido w u) (enLaFibra (.inl (b,r)))=
      masaAuxiliar w (.inl (b,r)) u := by
  unfold masaAuxiliar
  change _=retenidaPor _ lineasPropias _
  rw [retener_las_dos_es_la_mascara_fisica]
  unfold masaBajo
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : enLaFibra (.inl (b,r)) e <;> by_cases k : quedaTrasReserva u e <;>
    simp [pesoCuando,pesoEnLaFibra,pesoRetenido,h,k]

theorem las_filas_particionan_el_peso {n} (w : Cell n→ℝ) :
    (∑ r : Fin n,masaBajo w (enLaFibra (.inl (false,r))))=∑ e : Cell n,w e := by
  unfold masaBajo pesoCuando
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [enLaFibra]
  rw [Finset.sum_eq_single_of_mem e.1 (Finset.mem_univ _)]
  · simp
  · intro r _ ne
    simp [Ne.symm ne]

theorem desviacion_total_por_las_filas {n} (w : Cell n→ℝ) (u : LineaReservable n→Bool) (τ t : ℝ)
    (rows : ∀ r,|masaAuxiliar w (.inl (false,r)) u-centroDeLaFibra τ w (.inl (false,r))|≤t) :
    |(∑ e : Cell n,pesoRetenido w u e)-(1-τ)^2*(∑ e : Cell n,w e)|≤(n:ℝ)*t := by
  rw [←las_filas_particionan_el_peso (pesoRetenido w u),←las_filas_particionan_el_peso w,Finset.mul_sum,
    ←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have each (r : Fin n) : |masaBajo (pesoRetenido w u) (enLaFibra (.inl (false,r)))-
      (1-τ)^2*masaBajo w (enLaFibra (.inl (false,r)))|≤t := by
    rw [masa_de_fila_o_columna_es_auxiliar]
    exact rows r
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun r _=>each r)

theorem masa_escalar {n} (w : Cell n→ℝ) (P : Cell n→Prop) (b : ℝ) :
    masaBajo (fun e=>b*w e) P=b*masaBajo w P := by
  unfold masaBajo
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : P e <;> simp [pesoCuando,h]

theorem admisibilidad_de_la_reserva_fisica {n} (w : Cell n→ℝ) (u : LineaReservable n→Bool)
    (q τ t σ L A : ℝ) (qn : 0<q) (half : (n:ℝ)≤2*q) (capQ : q≤n)
    (qmass : (∑ e : Cell n,w e)=q) (pt : 0≤τ) (tiny : τ≤L/8) (s0 : 0≤σ) (sl : σ≤L) (l1 : L≤1)
    (tn : 0≤t) (ht : t≤σ/100) (pos : ∀ e,0≤w e) (cell : ∀ e,w e≤A)
    (rc : ∀ i : Bool × Fin n,masaBajo w (enLaFibra (.inl i))≤1-σ/2)
    (ob : ∀ j : LineaReservable n,masaBajo w (enLaFibra (.inr j))≤1-3*L/4)
    (reg : ∀ i,|masaAuxiliar w i u-centroDeLaFibra τ w i|≤t) :
    let X:=∑ e : Cell n,pesoRetenido w u e
    let v:=fun e=>(q/X)*pesoRetenido w u e
    0<X ∧ 1≤q/X ∧ q/X≤2 ∧ (∑ e : Cell n,v e)=q ∧ (∀ e,0≤v e ∧ v e≤2*A) ∧
      (∀ i,masaBajo v (enLaFibra i)≤1-σ/4) ∧ q-X≤(2*τ+t)*n := by
  dsimp only
  let X:=∑ e : Cell n,pesoRetenido w u e
  have loss (e : Cell n) : 0≤pesoRetenido w u e ∧ pesoRetenido w u e≤w e := by
    unfold pesoRetenido
    split <;> simp [pos]
  have lx : X≤q := (Finset.sum_le_sum (s:=Finset.univ) (fun e _=>(loss e).2)).trans_eq qmass
  have total:=desviacion_total_por_las_filas w u τ t (fun r=>reg (.inl (false,r)))
  rw [qmass] at total
  obtain ⟨xp,f1,f2,drop,key⟩:=control_del_normalizador (X:=X) qn half capQ pt
    (show τ≤1/8 by linarith only [tiny,l1]) (sl.trans l1) tn ht lx total
  refine ⟨xp,f1,f2,?_,?_,?_,drop⟩
  · rw [←Finset.mul_sum]
    change q/X*X=q
    exact div_mul_cancel₀ q xp.ne'
  · intro e
    have non : 0≤q/X := div_nonneg qn.le xp.le
    exact ⟨mul_nonneg non (loss e).1,
      (mul_le_mul_of_nonneg_right f2 (loss e).1).trans (mul_le_mul_of_nonneg_left ((loss e).2.trans (cell e)) (by norm_num))⟩
  · intro i
    rw [masa_escalar]
    have upper:=(abs_le.mp (reg i)).2
    rcases i with ⟨b,r⟩|j
    · rw [masa_de_fila_o_columna_es_auxiliar]
      change masaAuxiliar w (.inl (b,r)) u-(1-τ)^2*masaBajo w (enLaFibra (.inl (b,r)))≤t at upper
      exact fila_conserva_holgura_al_normalizar qn xp (by linarith only [tiny,l1])
        s0 (sl.trans l1) tn ht key (rc (b,r)) (by linarith only [upper])
    · change (q/X)*masaBajo (fun e=>if quedaTrasReserva u e then w e else 0) _ ≤ _
      rw [masa_efectiva_de_la_oblicua]
      split
      · apply oblicua_conserva_holgura_al_normalizar qn xp pt tiny s0 sl l1 tn ht key (ob j)
        change masaAuxiliar w (.inr j) u-(1-τ)^1*masaBajo w (enLaFibra (.inr j))≤t at upper
        rw [pow_one] at upper
        linarith only [upper]
      · rw [mul_zero]
        linarith only [sl,l1]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.admisibilidad_de_la_reserva_fisica
