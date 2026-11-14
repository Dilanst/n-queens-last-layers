import ContinuidadDeLasCuatroCavidadesMedibles
import ConjuntosNulosDeLasCuatroEtiquetas
import RepresentanteFisicoDeLosCuatroLimites
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open scoped Topology
theorem euler_fisica_desde_vacancias_medibles {P : TableroMedido} {x : ℝ≥0} (xp : 0<(x:ℝ))
    {a : ℝ} (ap : 0<a) (mass : P.rho=1-(x:ℝ)) {f : Fin 4→ℝ→ℝ}
    (fi : ∀ i,Integrable (f i)) (fm : ∀ i,Measurable (f i)) (nn : ∀ i y,0≤f i y)
    (cap : ∀ i y,|f i y|≤1)
    (area : ∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=a*f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z))
    (line : ∀ i,∀ᵐ s ∂marginalRef i,P.u i s=f i s)
    (fiber : ∀ i,∀ᵐ s ∂marginalRef i,f i s*(1+a*cavidadFisica f i s)=1) :
    ∃ p : FactoresContinuos,EulerFisica P p x (a*(x:ℝ)^2) ∧
      (∀ i,Continuous (camposFisicos p i)) ∧ ∀ i,∀ s∈rangoF i,0<camposFisicos p i s := by
  let q i s:=1/(1+a*cavidadFisica f i s)
  let v i s:=q i s/coefLinea x i
  let p:=factoresEnElExtremo v
  have coeff (i : Fin 4) : 0<coefLinea x i := by unfold coefLinea; split <;> first | exact xp | exact zero_lt_one
  have rep i:=representante_por_la_cavidad fi fm 1 cap nn ap i
  have vc i : ContinuousOn (v i) (rangoF i) := (rep i).1.div_const _
  have vp i s (hs : s∈rangoF i) : 0<v i s := div_pos ((rep i).2 s hs).1 (coeff i)
  have vn i s (hs : s∈rangoF i) := (vp i s hs).le
  have pc i : Continuous (camposFisicos p i) := representante_continuo_sobre_la_recta vc vn i
  have point i s (hs : s∈rangoF i) := representante_en_su_intervalo vn i hs
  have vac i : ∀ᵐ s ∂marginalRef i,f i s=coefLinea x i*camposFisicos p i s := by
    filter_upwards [fiber i,linea_en_dominio i] with s eq hs
    rw [point i s hs]
    have den : 1+a*cavidadFisica f i s≠0 := fun hz=>by rw [hz,mul_zero] at eq; exact zero_ne_one eq
    have fq : f i s=q i s := (eq_div_iff den).mpr eq
    rw [fq]; dsimp only [v]; field_simp [(coeff i).ne']
  have cell i : ∀ᵐ z ∂cuadrado,f i (coord i z)=coefLinea x i*camposFisicos p i (coord i z) :=
    etiqueta_cumple_en_el_tablero i (S:={s | f i s=coefLinea x i*camposFisicos p i s})
      (measurableSet_eq_fun (fm i) (measurable_const.mul (pc i).measurable)) (vac i)
  refine ⟨p,⟨mul_pos ap (sq_pos_of_pos xp),mass,?_,?_⟩,pc,?_⟩
  · filter_upwards [area,cell 0,cell 1,cell 2,cell 3] with z hz e0 e1 e2 e3
    rw [hz,e0,e1,e2,e3]
    norm_num [coefLinea,camposFisicos,factorF,coord,pesoContinuo,show ¬(3:Fin 4).val<2 by decide]; ring
  · intro i; filter_upwards [line i,vac i] with s hi eq; exact hi.trans eq
  · intro i s hs; rw [point i s hs]; exact vp i s hs
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_fisica_desde_vacancias_medibles
