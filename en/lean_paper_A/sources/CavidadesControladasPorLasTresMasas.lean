import MasaYEnergiaDeUnaCuerda
import IntegracionDeLasTresDiferencias
import DiferenciaDelProductoDeTresFactores
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set MeasureTheory
open scoped Interval
def sumaTransversal (i : Fin 4) (v : Fin 4→ℝ) :=
  v (familiaTransversal i 0)+v (familiaTransversal i 1)+v (familiaTransversal i 2)

theorem control_de_la_cavidad_por_L1 {p q : Fin 4→ℝ→ℝ} {K : ℝ}
    (cp : ∀ g,ContinuousOn (p g) (rangoF g)) (cq : ∀ g,ContinuousOn (q g) (rangoF g))
    (bp : ∀ g,∀ y∈rangoF g,|p g y|≤K) (bq : ∀ g,∀ y∈rangoF g,|q g y|≤K)
    (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    |cavidadFisica p i s-cavidadFisica q i s|≤K^2*sumaTransversal i
      (masaExterior (fun g y=>|p g y-q g y|)) := by
  let v : Fin 4→ℝ→ℝ:=fun g y=>|p g y-q g y|
  have cv : ∀ g,ContinuousOn (v g) (rangoF g) := fun g=>( (cp g).sub (cq g)).abs
  have per:=fun j=>masa_en_cuerda_fisica cv (fun _ _=>abs_nonneg _) i hs j
  apply (integra_tres_errores (longitud_en_unidad i hs).1
    (producto_continuo_sobre_la_cuerda cp i hs) (producto_continuo_sobre_la_cuerda cq i hs)
    (fun j=>campo_continuo_sobre_la_cuerda cv i hs j) ?_).trans
  · exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (per 0) (per 1)) (per 2)) (sq_nonneg K)
  · intro t ht
    exact diferencia_producto_tres (restriccionACuerda p i s t) (restriccionACuerda q i s t)
      (fun j=>bp _ _ (etiqueta_en_el_intervalo_fisico i j hs ht))
      (fun j=>bq _ _ (etiqueta_en_el_intervalo_fisico i j hs ht))

theorem suma_de_tres_acotada_por_las_cuatro (i : Fin 4) (v : Fin 4→ℝ) (hv : ∀ g,0≤v g) :
    sumaTransversal i v ≤ ∑ g,v g := by
  fin_cases i <;> simp [Fin.sum_univ_four,sumaTransversal,familiaTransversal] <;>
    linarith [hv 0,hv 1,hv 2,hv 3]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_de_la_cavidad_por_L1
#print axioms ArticuloA.Historias.suma_de_tres_acotada_por_las_cuatro
