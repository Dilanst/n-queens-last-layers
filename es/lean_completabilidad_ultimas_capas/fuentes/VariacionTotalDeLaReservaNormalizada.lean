import NormalizacionFisicaDeLaReserva
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

theorem variacion_total_despues_de_normalizar {n} (w : Cell n→ℝ) (u : LineaReservable n→Bool)
    (q X : ℝ) (p : ∀ e,0≤w e) (mass : ∑ e : Cell n,w e=q) (ret : ∑ e : Cell n,pesoRetenido w u e=X)
    (xp : 0<X) (loss : X≤q) :
    (∑ e : Cell n,|(q/X)*pesoRetenido w u e-w e|)=2*(q-X) := by
  have ge : 1≤q/X := (le_div_iff₀ xp).mpr (by simpa using loss)
  have pointw (e : Cell n) : |(q/X)*pesoRetenido w u e-w e|=
      (w e-pesoRetenido w u e)+(q/X-1)*pesoRetenido w u e := by
    by_cases he : quedaTrasReserva u e
    · have h:=mul_nonneg (sub_nonneg.mpr ge) (p e)
      simp only [pesoRetenido,if_pos he,sub_self,zero_add]
      rw [abs_of_nonneg (by linarith only [h])]
      ring
    · simp [pesoRetenido,he,abs_of_nonneg (p e)]
  simp_rw [pointw]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,mass,ret]
  field_simp [xp.ne']
  ring

theorem variacion_de_una_fibra {n} (v w : Cell n→ℝ) (P : Cell n→Prop) :
    |masaBajo v P-masaBajo w P|≤masaBajo (fun e=>|v e-w e|) P := by
  unfold masaBajo
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  by_cases h : P e <;> simp [pesoCuando,h]

theorem una_casilla_tiene_cuatro_incidencias {n} (e : Cell n) (v : ℝ) :
    (∑ i : FibraDeB1 n,pesoCuando (enLaFibra i e) v)=4*v := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,enLaFibra,pesoCuando]
  have pick {m : ℕ} (p : Fin m) (f : Fin m→ℝ) (atp : f p=v)
      (off : ∀ r,r≠p→f r=0) : (∑ i,f i)=v := by
    rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ _)]
    · exact atp
    · exact fun r _ ne=>off r ne
  calc
    _ = (v+v)+(v+v) := by
      apply congrArg₂ (·+·)
      · apply congrArg₂ (·+·)
        · apply pick e.2
          · simp
          · intro r ne; simp [Ne.symm ne]
        · apply pick e.1
          · simp
          · intro r ne; simp [Ne.symm ne]
      · apply congrArg₂ (·+·)
        · apply pick (etiquetaA e).2
          · simp [etiquetaA]
          · intro j hj
            have h : (etiquetaA e).2≠j:=Ne.symm hj
            simpa [etiquetaA] using (if_neg h : (if (etiquetaA e).2=j then v else 0)=0)
        · apply pick (etiquetaD e).2
          · simp [etiquetaD]
          · intro j hj
            have h : (etiquetaD e).2≠j:=Ne.symm hj
            simpa [etiquetaD] using (if_neg h : (if (etiquetaD e).2=j then v else 0)=0)
    _ = _ := by ring

theorem las_masas_de_linea_suman_cuatro_veces_la_de_casilla {n} (w : Cell n→ℝ) :
    (∑ i : FibraDeB1 n,masaBajo w (enLaFibra i))=4*∑ e : Cell n,w e := by
  unfold masaBajo
  rw [Finset.sum_comm,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _=>una_casilla_tiene_cuatro_incidencias e (w e))

theorem variacion_agregada_para_la_entropia_de_lineas {n} (v w : Cell n→ℝ) :
    (∑ i : FibraDeB1 n,|masaBajo v (enLaFibra i)-masaBajo w (enLaFibra i)|)≤4*∑ e : Cell n,|v e-w e| := by
  rw [←las_masas_de_linea_suman_cuatro_veces_la_de_casilla]
  exact Finset.sum_le_sum (fun i _=>variacion_de_una_fibra v w (enLaFibra i))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.variacion_total_despues_de_normalizar
#print axioms ArticuloA.Historias.variacion_agregada_para_la_entropia_de_lineas
