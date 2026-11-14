import MediasDeLasFibrasDespuesDeReservar
namespace ArticuloA.Historias
open Repair Limites
noncomputable section
open Classical
open scoped BigOperators

/-- A change of bit j reaches only one square of nonzero weight in the fiber. -/
theorem una_casilla_por_bit_basta {n} (w : Cell n→ℝ) (S : Cell n→Finset (LineaReservable n))
    (B : ℝ) (bn : 0≤B) (cap : ∀ e,|w e|≤B)
    (una : ∀ j e f,w e≠0→w f≠0→j∈S e→j∈S f→e=f) :
    oscilacionPorBit (retenidaPor w S) B := by
  intro j ω v off
  let val (u : LineaReservable n→Bool) (e : Cell n) :=
    if acuerdoDeReserva ∅ (S e) u then w e else 0
  have quiet (e : Cell n) (h : ¬(w e≠0 ∧ j∈S e)) : val ω e-val v e=0 := by
    by_cases z : w e=0
    · simp [val,z]
    · have outside : j∉S e := fun hj=>h ⟨z,hj⟩
      have equiv:=acuerdo_igual_fuera_de_las_etiquetas ∅ (S e) ω v j off (by simp) outside
      by_cases yes : acuerdoDeReserva ∅ (S e) ω
      · simp [val,yes,equiv.mp yes]
      · have nv : ¬acuerdoDeReserva ∅ (S e) v := fun hv=>yes (equiv.mpr hv)
        simp [val,yes,nv]
  change |(∑ e,val ω e)-(∑ e,val v e)|≤B
  rw [←Finset.sum_sub_distrib]
  by_cases exi : ∃ e,w e≠0 ∧ j∈S e
  · obtain ⟨e,ne,hit⟩:=exi
    rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
    · by_cases a : acuerdoDeReserva ∅ (S e) ω <;> by_cases b : acuerdoDeReserva ∅ (S e) v <;>
        simp [val,a,b,bn,cap]
    · intro f _ diff
      exact quiet f (fun hf=>diff (una j f e hf.1 ne hf.2 hit))
  · have zeros (e : Cell n) : val ω e-val v e=0:=quiet e (fun h=>exi ⟨e,h⟩)
    simp [zeros,bn]

theorem la_misma_oblicua_corta_una_fila_o_columna {n} (j : LineaReservable n) (e f : Cell n)
    (he : j∈lineasPropias e) (hf : j∈lineasPropias f) : (e.1=f.1 ∨ e.2=f.2) → e=f := by
  have ec:=e.2.isLt
  have fc:=f.2.isLt
  intro axis
  simp only [lineasPropias,Finset.mem_insert,Finset.mem_singleton] at he hf
  rcases he with he|he <;> rcases hf with hf|hf <;> subst j <;>
    simp [etiquetaD,etiquetaA,Fin.ext_iff] at hf <;> apply Prod.ext <;> apply Fin.ext <;>
    rcases axis with h|h <;> have hx:=congrArg Fin.val h <;> omega

theorem oscila_una_fila_o_columna {n} (w : Cell n→ℝ) (B : ℝ) (bn : 0≤B)
    (cap : ∀ e,|w e|≤B) (fibra : ∀ e f,w e≠0→w f≠0→e.1=f.1 ∨ e.2=f.2) :
    oscilacionPorBit (retenidaPor w lineasPropias) B :=
  una_casilla_por_bit_basta w _ B bn cap (fun j e f he hf a b=>
    la_misma_oblicua_corta_una_fila_o_columna j e f a b (fibra e f he hf))

theorem el_cruce_de_dos_oblicuas_es_unico {n} (e f : Cell n)
    (hd : etiquetaD e=etiquetaD f) (ha : etiquetaA e=etiquetaA f) : e=f := by
  have ec:=e.2.isLt
  have fc:=f.2.isLt
  simp [etiquetaD,etiquetaA,Fin.ext_iff] at hd ha
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem oscila_una_oblicua_sin_su_bit {n} (w : Cell n→ℝ) (B : ℝ) (bn : 0≤B)
    (cap : ∀ e,|w e|≤B) (d : Bool) (linea : ∀ e f,w e≠0→w f≠0→
      (if d then etiquetaD e else etiquetaA e)=(if d then etiquetaD f else etiquetaA f)) :
    oscilacionPorBit (retenidaPor w (fun e=>{if d then etiquetaA e else etiquetaD e})) B := by
  apply una_casilla_por_bit_basta w _ B bn cap
  intro j e f he hf a b
  have same:=linea e f he hf
  cases d <;> simp only [Bool.false_eq_true,if_false,if_true,Finset.mem_singleton] at a b same
  · exact el_cruce_de_dos_oblicuas_es_unico e f (a.symm.trans b) same
  · exact el_cruce_de_dos_oblicuas_es_unico e f same (a.symm.trans b)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.oscila_una_fila_o_columna
#print axioms ArticuloA.Historias.oscila_una_oblicua_sin_su_bit
