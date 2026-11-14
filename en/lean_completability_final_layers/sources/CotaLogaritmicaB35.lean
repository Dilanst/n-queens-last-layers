import CavidadesControladasPorLasTresMasas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Set MeasureTheory
open scoped Interval
def energiaDeDiferencias (v w : Fin 4→ℝ→ℝ) (g : Fin 4) :=
  masaExterior (fun i y=>(v i y-w i y)^2) g

theorem estimacion_fisica_B35 {v w : Fin 4→ℝ→ℝ} {K : ℝ}
    (cv : ∀ g,ContinuousOn (v g) (rangoF g)) (cw : ∀ g,ContinuousOn (w g) (rangoF g))
    (bv : ∀ g,∀ y∈rangoF g,Real.exp (v g y)≤K) (bw : ∀ g,∀ y∈rangoF g,Real.exp (w g y)≤K)
    (i : Fin 4) {s : ℝ} (hs : s∈rangoF i) :
    |cavidadFisica (fun g y=>Real.exp (v g y)) i s-cavidadFisica (fun g y=>Real.exp (w g y)) i s|≤
      Real.sqrt 3*K^3*Real.sqrt (∑ g,energiaDeDiferencias v w g) := by
  let D : Fin 4→ℝ→ℝ:=fun g y=>v g y-w g y
  let a:=energiaDeDiferencias v w
  have cd : ∀ g,ContinuousOn (D g) (rangoF g) := fun g=>(cv g).sub (cw g)
  have per (j : Fin 3) := energia_en_cuerda_fisica cd i hs j
  have pos : ∀ g,0≤a g := masa_exterior_no_negativa (fun g y=>sq_nonneg (D g y))
  have hk : 0≤K := (Real.exp_pos _).le.trans (bv i s hs)
  let f := fun g y=>Real.exp (v g y)
  let h := fun g y=>Real.exp (w g y)
  have cf : ∀ g,ContinuousOn (f g) (rangoF g) := fun g=>Real.continuous_exp.comp_continuousOn (cv g)
  have ch : ∀ g,ContinuousOn (h g) (rangoF g) := fun g=>Real.continuous_exp.comp_continuousOn (cw g)
  have point (t : ℝ) (ht : t∈Icc 0 (longitudDeCuerda i s)) :
      |productoEnCuerda f i s t-productoEnCuerda h i s t|≤K^3*
        (|restriccionACuerda D i s t 0|+|restriccionACuerda D i s t 1|+|restriccionACuerda D i s t 2|) := by
    have ev (j : Fin 3) := bv _ _ (etiqueta_en_el_intervalo_fisico i j hs ht)
    have ew (j : Fin 3) := bw _ _ (etiqueta_en_el_intervalo_fisico i j hs ht)
    have diff (j : Fin 3) : |restriccionACuerda f i s t j-restriccionACuerda h i s t j|≤
        K*|restriccionACuerda D i s t j| := diferencia_exponencial_desde_arriba (ev j) (ew j)
    apply (diferencia_producto_tres (restriccionACuerda f i s t) (restriccionACuerda h i s t)
      (fun j=>(abs_of_pos (Real.exp_pos _)).symm ▸ ev j)
      (fun j=>(abs_of_pos (Real.exp_pos _)).symm ▸ ew j)).trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add (diff 0) (diff 1)) (diff 2)) (sq_nonneg K)).trans_eq (by ring)
  have base:=integra_tres_errores (longitud_en_unidad i hs).1
    (producto_continuo_sobre_la_cuerda cf i hs) (producto_continuo_sobre_la_cuerda ch i hs)
    (fun j=>(campo_continuo_sobre_la_cuerda cd i hs j).abs) point
  have roots := suma_de_tres_raices (pos (familiaTransversal i 0)) (pos (familiaTransversal i 1)) (pos (familiaTransversal i 2))
  have three : sumaTransversal i a≤∑ g,a g := suma_de_tres_acotada_por_las_cuatro i a pos
  have total := roots.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt three) (Real.sqrt_nonneg 3))
  apply base.trans
  exact (mul_le_mul_of_nonneg_left ((add_le_add (add_le_add (per 0) (per 1)) (per 2)).trans total)
    (pow_nonneg hk 3)).trans_eq (by ring)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.estimacion_fisica_B35
