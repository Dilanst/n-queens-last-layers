import LogaritmosDelPerfil
import ProductoDeCuatroFactores
open Set
open scoped NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

structure ControlEspacial (p : FactoresContinuos) (κ M L : ℝ) : Prop where
  R : RegularEn unidadCerrada p.fila κ L
  C : RegularEn unidadCerrada p.columna κ L
  D : RegularEn (Icc (-1) 1) p.diagonal κ L
  A : RegularEn (Icc 0 2) p.anti κ L
  Rmax : ∀ z∈unidadCerrada,(p.fila z:ℝ)≤M
  Cmax : ∀ z∈unidadCerrada,(p.columna z:ℝ)≤M
  Dmax : ∀ z∈Icc (-1) 1,(p.diagonal z:ℝ)≤M
  Amax : ∀ z∈Icc 0 2,(p.anti z:ℝ)≤M

private def cuatro (p : FactoresContinuos) (r c : ℝ) : Fin 4→ℝ
  | 0 => p.fila r
  | 1 => p.columna c
  | 2 => p.diagonal (r-c)
  | 3 => p.anti (r+c)

theorem dominios (r c : ℝ) (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    r-c∈Icc (-1) 1 ∧ r+c∈Icc 0 2 := by
  rcases hr with ⟨r0,r1⟩; rcases hc with ⟨c0,c1⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

private theorem mayores {p κ M L} (c : ControlEspacial p κ M L) (r t : ℝ)
    (hr : r∈unidadCerrada) (ht : t∈unidadCerrada) : ∀ j,|cuatro p r t j|≤M := by
  obtain ⟨d,a⟩ := dominios _ _ hr ht
  intro j; fin_cases j <;> simp only [cuatro,abs_of_nonneg (NNReal.coe_nonneg _)]
  exacts [c.Rmax _ hr,c.Cmax _ ht,c.Dmax _ d,c.Amax _ a]

theorem variacion_del_peso {p κ M L} (data : ControlEspacial p κ M L) (lp : 0≤L)
    (r s c j : ℝ) (hr : r∈unidadCerrada) (hs : s∈unidadCerrada) (hc : c∈unidadCerrada) (hj : j∈unidadCerrada) :
    |pesoContinuo p r c-pesoContinuo p s j|≤(4*M^3*L)*(|r-s|+|c-j|) := by
  obtain ⟨d0,a0⟩ := dominios _ _ hr hc
  obtain ⟨d1,a1⟩ := dominios _ _ hs hj
  have both (i : Fin 4) : |cuatro p r c i-cuatro p s j i|≤L*(|r-s|+|c-j|) := by
    fin_cases i
    · exact (data.R.oscilacion r hr s hs).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) lp)
    · exact (data.C.oscilacion c hc j hj).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) lp)
    · apply (data.D.oscilacion _ d0 _ d1).trans
      rw [show r-c-(s-j)=(r-s)-(c-j) by ring]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) lp
    · apply (data.A.oscilacion _ a0 _ a1).trans
      rw [show r+c-(s+j)=(r-s)+(c-j) by ring]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) lp
  exact (cuatro_factores _ _ M _ (mayores data _ _ hr hc) (mayores data _ _ hs hj) both).trans_eq (by ring)

theorem limites_del_producto {p κ M L} (data : ControlEspacial p κ M L) (kp : 0≤κ)
    (r c : ℝ) (hr : r∈unidadCerrada) (hc : c∈unidadCerrada) :
    κ^4≤pesoContinuo p r c ∧ pesoContinuo p r c≤M^4 := by
  obtain ⟨d,a⟩ := dominios r c hr hc
  have mp : 0≤M := (NNReal.coe_nonneg _).trans (data.Rmax _ hr)
  unfold pesoContinuo
  constructor
  · calc
      κ^4 = κ*κ*κ*κ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (mul_le_mul (data.R.minimo _ hr) (data.C.minimo _ hc) kp (NNReal.coe_nonneg _))
        (data.D.minimo _ d) kp (by positivity)) (data.A.minimo _ a) kp (by positivity)
  · calc
      _ ≤ M*M*M*M := mul_le_mul (mul_le_mul (mul_le_mul (data.Rmax _ hr) (data.Cmax _ hc) (NNReal.coe_nonneg _) mp)
        (data.Dmax _ d) (NNReal.coe_nonneg _) (mul_nonneg mp mp)) (data.Amax _ a) (NNReal.coe_nonneg _) (by positivity)
      _ = _ := by ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.variacion_del_peso
#print axioms ArticuloA.Historias.limites_del_producto
