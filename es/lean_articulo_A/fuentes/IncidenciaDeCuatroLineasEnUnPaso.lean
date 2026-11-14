import HolguraTemporalDelPesoDeGTrasFijarLaReserva
namespace ArticuloA.Historias
open Repair
open scoped BigOperators
noncomputable section
open Classical

theorem dos_familias_determinan_la_casilla {n} {a b : Cell n} {i j : Fin 4}
    (dif : i≠j) (hi : llaveDeLinea i a=llaveDeLinea i b)
    (hj : llaveDeLinea j a=llaveDeLinea j b) : a=b := by
  apply Prod.ext <;> apply Fin.ext
  all_goals fin_cases i <;> fin_cases j <;> simp_all [llaveDeLinea] <;> omega

def riesgoDeLinea {n} (p : Cell n→ℝ) (c : Cell n) (i : Fin 4) : ℝ :=
  ∑ b : Cell n,if llaveDeLinea i b=llaveDeLinea i c then p b else 0

theorem incidencia_tras_una_eleccion {n} (b c : Cell n) (v : ℝ) :
    (if compatible c b then v else 0)=v-
      (∑ i : Fin 4,if llaveDeLinea i b=llaveDeLinea i c then v else 0)+
        3*(if b=c then v else 0) := by
  by_cases same : b=c
  · subst b
    have bad : ¬compatible c c:=fun h=>h.1 rfl
    simp [bad,Fin.sum_univ_four]; ring
  · rw [if_neg same]
    by_cases safe : compatible c b
    · have none (i : Fin 4) : llaveDeLinea i b≠llaveDeLinea i c :=
        Ne.symm ((compatible_iff_llaves _ _).mp safe i)
      simp [safe,none]
    · have one : ∃ i,llaveDeLinea i b=llaveDeLinea i c := by
        by_contra! no
        exact safe ((compatible_iff_llaves _ _).mpr (fun i=>(no i).symm))
      obtain ⟨i,hit⟩:=one
      have alone (j : Fin 4) (ne : j≠i) : llaveDeLinea j b≠llaveDeLinea j c :=
        fun eq=>same (dos_familias_determinan_la_casilla ne eq hit)
      have eqsum : (∑ j : Fin 4,if llaveDeLinea j b=llaveDeLinea j c then v else 0)=v := by
        rw [Finset.sum_eq_single i]
        · simp [hit]
        · intro j _ ne; simp [alone j ne]
        · simp
      simp [safe,eqsum]

theorem supervivencia_de_una_casilla {n} (p : Cell n→ℝ) (ley : ∑ b,p b=1) (c : Cell n) :
    (∑ b : Cell n,if compatible c b then p b else 0)=
    1-(∑ i : Fin 4,riesgoDeLinea p c i)+3*p c := by
  simp_rw [incidencia_tras_una_eleccion _ _ (p _)]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,ley,Finset.sum_comm]
  simp [riesgoDeLinea,←Finset.mul_sum]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.supervivencia_de_una_casilla
