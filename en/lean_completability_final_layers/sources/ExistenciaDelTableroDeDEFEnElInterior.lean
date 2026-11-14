import EulerDeUnaLineaEnElMinimo
import TableroFisicoDesdeLasFibrasNormalizadas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def DatosDelInterior (x : ℝ) (P : TableroMedido) (a : ℝ) (f : Fin 4→ℝ→ℝ) : Prop :=
  0<a ∧ P.rho=1-x ∧
      (∀ i,Integrable (f i)) ∧ (∀ i,Measurable (f i)) ∧ (∀ i y,0≤f i y) ∧ (∀ i y,|f i y|≤1) ∧
      (∀ᵐ z ∂cuadrado,(P.ν z:ℝ)=a*f 0 (coord 0 z)*f 1 (coord 1 z)*f 2 (coord 2 z)*f 3 (coord 3 z)) ∧
      ∀ i,∀ᵐ s ∂marginalRef i,P.u i s=f i s

theorem existencia_de_DEF_a_masa_fija {x : ℝ} (xp : 0<x) (xt : x<1) :
    ∃ P a f,DatosDelInterior x P a f := by
  let d:=1-x
  have dp : 0<d:=sub_pos.mpr xt
  have dt : d<1:=by dsimp only [d]; linarith
  let B:=d*exp (6/(1-d))
  let H:=log (1+B)+1
  have bp : 0<B:=mul_pos dp (exp_pos _)
  have hp : 0≤H:=by dsimp only [H]; linarith [log_nonneg (show 1≤1+B by linarith)]
  obtain ⟨u,minimal,_⟩:=minimo_unico_del_funcional_fisico hp dp dt
  obtain ⟨zero,zval⟩:=existe_competidor_de_valor_cero hp d
  have low:= (minimal zero).trans zval.le
  let a:=d/particionDual u
  have zp : 0<particionDual u := (exp_pos _).trans_le (particion_dual_acotada hp u).1
  have ap : 0<a := div_pos dp zp
  have bound : a≤B:=cota_de_escala_en_el_subnivel hp dp dt u low
  have margin : log (1+a)≤H := by
    apply (Real.log_le_log (by linarith only [ap]) (add_le_add_left bound 1)).trans
    dsimp only [H]; linarith
  let f:=vacanciaDeCampo (campoDual u)
  have fb:=vacancia_de_campo_en_unidad (campo_dual_acotado hp u)
  have fm:=vacancia_de_campo_medible (campo_dual_medible u)
  have Z:=particion_en_producto_crudo u (campo_dual_medible u) (fun _=>EventuallyEq.rfl)
  have mass : a*(∫ z,productoCuatroFisico f z ∂cuadrado)=d := by rw [←Z]; exact div_mul_cancel₀ _ zp.ne'
  obtain ⟨P,ρ,area,line⟩:=tablero_desde_fibras_normalizadas ap fb fm mass (euler_de_una_linea_en_el_minimo hp dp u minimal margin)
  exact ⟨P,a,f,ap,ρ,vacancia_de_campo_integrable (campo_dual_medible u) (campo_dual_acotado hp u),fm,
    fun i s=>(fb i s).1,fun i s=>(abs_of_nonneg (fb i s).1).le.trans (fb i s).2,area,line⟩

theorem existencia_de_la_rama_medible_de_DEF :
    ∃ (P : ℝ→TableroMedido) (a : ℝ→ℝ) (f : ℝ→Fin 4→ℝ→ℝ),∀ x∈Ioc (0:ℝ) (1/2),DatosDelInterior x (P x) (a x) (f x) := by
  classical
  let t (x : ℝ):=if x∈Ioc (0:ℝ) (1/2) then x else 1/2
  have admissible x : 0<t x ∧ t x<1 := by
    by_cases h : x∈Ioc (0:ℝ) (1/2)
    · simp only [t,if_pos h]; exact ⟨h.1,h.2.trans_lt (by norm_num)⟩
    · simp only [t,if_neg h]; norm_num
  choose P a f hf using fun x=>existencia_de_DEF_a_masa_fija (admissible x).1 (admissible x).2
  exact ⟨P,a,f,fun x hx=>by simpa only [t,if_pos hx] using hf x⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.existencia_de_DEF_a_masa_fija
#print axioms ArticuloA.Historias.existencia_de_la_rama_medible_de_DEF
