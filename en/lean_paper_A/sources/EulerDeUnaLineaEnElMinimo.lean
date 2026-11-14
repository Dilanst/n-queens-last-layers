import PrincipioDeComparacionPorUnaLinea
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem euler_de_una_linea_en_el_minimo {H d : ℝ} (hp : 0≤H) (dp : 0<d) (u : CajaDual H)
    (minimal : ∀ v : CajaDual H,funcionalDual d u≤funcionalDual d v)
    (margin : log (1+d/particionDual u)≤H) (i : Fin 4) :
    let a:=d/particionDual u
    let f:=vacanciaDeCampo (campoDual u)
    ∀ᵐ s ∂marginalRef i,1-f i s=a*(f i s*cavidadFisica f i s) := by
  let a:=d/particionDual u
  let K:=seccionDelDual u i
  let A (s : ℝ):=1+a*K s
  let w s:=log (A s)
  let g:=campoDual u i
  have ap : 0<a:=div_pos dp ((exp_pos _).trans_le (particion_dual_acotada hp u).1)
  have low s : 1≤A s := le_add_of_nonneg_right (mul_nonneg ap.le (seccion_del_dual_en_unidad hp u i s).1)
  have pos s : 0<A s:=zero_lt_one.trans_le (low s)
  have wm : Measurable w := (measurable_const.add (measurable_const.mul (seccion_del_dual_continua hp u i).measurable)).log
  have wb s : w s∈Icc 0 H := by
    refine ⟨log_nonneg (low s),(Real.log_le_log (pos s) ?_).trans margin⟩
    exact add_le_add_left (mul_le_of_le_one_right ap.le (seccion_del_dual_en_unidad hp u i s).2) 1
  let Ew:=energiaEnSeccion a K w
  let Eg:=energiaEnSeccion a K g
  have minInt : (∫ s,Eg s ∂marginalRef i)≤∫ s,Ew s ∂marginalRef i :=
    energia_de_seccion_minima hp dp u minimal i wm wb
  have align (v : ℝ→ℝ) s : energiaEnSeccion a K v s=v s+A s*exp (-v s)-1 := by
    unfold energiaEnSeccion potencialDeHolgura A; ring
  have per s:=ecuacion_puntual_del_mayorante (pos s) (g s)
  have ord s : Ew s≤Eg s := by
    dsimp only [Ew,Eg]; rw [align,align]; dsimp only [w]; linarith only [(per s).1]
  have ei:= (energia_de_seccion_integrable (a:=a) hp u i wm wb).1
  have gi:= (energia_de_seccion_integrable (a:=a) hp u i (campo_dual_medible u i) (campo_dual_acotado hp u i)).1
  have equal : (∫ s,Eg s ∂marginalRef i)=∫ s,Ew s ∂marginalRef i :=
    le_antisymm minInt (integral_mono ei gi ord)
  have gap : (fun s=>Eg s-Ew s)=ᵐ[marginalRef i] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (fun s=>sub_nonneg.mpr (ord s))) (gi.sub ei)).mp
    change (∫ s,Eg s-Ew s ∂marginalRef i)=0
    rw [integral_sub gi ei,equal,sub_self]
  filter_upwards [gap,linea_en_dominio i] with s h hs
  change Eg s-Ew s=0 at h
  dsimp only [Eg,Ew] at h
  rw [align,align] at h
  have fixed : g s=log (A s) := (per s).2 (by change g s+A s*exp (-g s)-1-(log (A s)+A s*exp (-log (A s))-1)=0 at h; linarith only [h])
  change 1-vacanciaDeCampo (campoDual u) i s=a*(vacanciaDeCampo (campoDual u) i s*cavidadFisica (vacanciaDeCampo (campoDual u)) i s)
  have free : vacanciaDeCampo (campoDual u) i s=(A s)⁻¹ := by
    rw [vacanciaDeCampo,indicator_of_mem hs]; change exp (-g s)=(A s)⁻¹; rw [fixed,exp_neg,exp_log (pos s)]
  rw [free]
  have fibra : cavidadFisica (vacanciaDeCampo (campoDual u)) i s=K s := by dsimp [K,seccionDelDual]; rw [recorte_fijo i hs]
  rw [fibra]; field_simp [(pos s).ne']; dsimp [A]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.euler_de_una_linea_en_el_minimo
