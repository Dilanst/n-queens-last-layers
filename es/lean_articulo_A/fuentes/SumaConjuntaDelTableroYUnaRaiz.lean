import SeguimientoHastaUnaRaizVivaDelCaminoFisico
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def umbralDePrefijo (q : ℕ) (η A : ℝ) : ℕ→ℝ
  | 0=>A
  | j+1=>umbralDePrefijo q η A j+(9/((q:ℝ)-(1-η)*j))*umbralDePrefijo q η A j

theorem umbral_es_suma_de_prefijo (q : ℕ) (η A : ℝ) (j : ℕ) :
    umbralDePrefijo q η A j=A+∑ s∈Finset.range j,(9/((q:ℝ)-(1-η)*s))*umbralDePrefijo q η A s := by
  induction j with
  | zero=>simp [umbralDePrefijo]
  | succ j ih=>rw [umbralDePrefijo,Finset.sum_range_succ,←add_assoc,←ih]

theorem techo_del_umbral {q t : ℕ} {η A : ℝ} (qp : 0<q) (tq : t≤q) (hp : 0<η)
    (h4 : η≤1/4) (an : 0≤A) : umbralDePrefijo q η A t≤A*(1/η)^12 :=
  envolvente_de_seguimiento_hasta_la_parada qp tq hp h4 an _ (fun j _=>(umbral_es_suma_de_prefijo q η A j).le)

theorem suma_de_dos_innovaciones_y_derivas {t : ℕ} {q mw mz W Z cw cz : ℝ} (qp : 0<q)
    (dw dz gain : ℕ→ℝ) (bw : |mw|≤cw) (bz : |mz|≤cz)
    (ew : mw+∑ j∈Finset.range t,dw j=W) (ez : mz+∑ j∈Finset.range t,dz j=Z)
    (bounds : ∀ j<t,|dw j|/q+|dz j|≤gain j) :
    |W|/q+|Z|≤cw/q+cz+∑ j∈Finset.range t,gain j := by
  have w : |W|≤cw+∑ j∈Finset.range t,|dw j|:=by
    rw [←ew]; exact (abs_add_le _ _).trans (add_le_add bw (Finset.abs_sum_le_sum_abs _ _))
  have z : |Z|≤cz+∑ j∈Finset.range t,|dz j|:=by
    rw [←ez]; exact (abs_add_le _ _).trans (add_le_add bz (Finset.abs_sum_le_sum_abs _ _))
  have b:=Finset.sum_le_sum (fun j (hj : j∈Finset.range t)=>bounds j (Finset.mem_range.mp hj))
  rw [Finset.sum_add_distrib,←Finset.sum_div] at b
  have h:=div_le_div_of_nonneg_right w qp.le
  rw [add_div] at h
  linarith only [h,z,b]

theorem absorber_resto_constante_en_umbral {q t : ℕ} {η A cw cz R : ℝ}
    (tq : t≤q) (rn : 0≤R) (budget : cw/(q:ℝ)+cz+(22/10)*q*R≤A) :
    cw/(q:ℝ)+cz+(∑ j∈Finset.range t,((9/((q:ℝ)-(1-η)*j))*umbralDePrefijo q η A j+(22/10)*R))
      ≤umbralDePrefijo q η A t := by
  rw [umbral_es_suma_de_prefijo q η A t,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have le:=mul_le_mul_of_nonneg_right (show (t:ℝ)≤q by exact_mod_cast tq) rn
  linarith only [le,budget]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_de_dos_innovaciones_y_derivas
#print axioms ArticuloA.Historias.absorber_resto_constante_en_umbral
