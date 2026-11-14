import ReemplazoDeUnPotencialEnLaCaja
import MinimoDelFuncionalFisicoYMayorante
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

def energiaEnSeccion (a : ℝ) (K w : ℝ→ℝ) (s : ℝ) :=
  potencialDeHolgura (w s)+a*(exp (-w s)*K s)

theorem energia_de_seccion_integrable {H a : ℝ} (hp : 0≤H) (u : CajaDual H) (i : Fin 4)
    {w : ℝ→ℝ} (wm : Measurable w) (wb : ∀ s,w s∈Icc 0 H) :
    Integrable (energiaEnSeccion a (seccionDelDual u i) w) (marginalRef i) ∧
    (∫ s,energiaEnSeccion a (seccionDelDual u i) w s ∂marginalRef i)=
      (∫ s,potencialDeHolgura (w s) ∂marginalRef i)+a*(∫ s,exp (-w s)*seccionDelDual u i s ∂marginalRef i) := by
  let K:=seccionDelDual u i
  have wi : Integrable (fun s=>potencialDeHolgura (w s)) (marginalRef i) := by
    apply integral_acotada_dual ((wm.add wm.neg.exp).sub measurable_const) (M:=H)
    intro s
    have t:=exp_le_one_iff.mpr (neg_nonpos.mpr (wb s).1)
    exact abs_le.mpr ⟨by linarith [add_one_le_exp (-w s)],by linarith [(wb s).2]⟩
  have ki : Integrable (fun s=>exp (-w s)*K s) (marginalRef i) := by
    apply integral_acotada_dual (wm.neg.exp.mul (seccion_del_dual_continua hp u i).measurable) (M:=1)
    intro s
    have h:=seccion_del_dual_en_unidad hp u i s
    rw [abs_of_nonneg (mul_nonneg (exp_pos _).le h.1)]
    exact mul_le_one₀ (exp_le_one_iff.mpr (neg_nonpos.mpr (wb s).1)) h.1 h.2
  refine ⟨wi.add (ki.const_mul a),?_⟩
  unfold energiaEnSeccion; rw [integral_add wi (ki.const_mul a),integral_const_mul]

theorem energia_de_seccion_minima {H d : ℝ} (hp : 0≤H) (dp : 0<d) (u : CajaDual H)
    (minimal : ∀ v : CajaDual H,funcionalDual d u≤funcionalDual d v) (i : Fin 4)
    {w : ℝ→ℝ} (wm : Measurable w) (wb : ∀ s,w s∈Icc 0 H) :
    let a:=d/particionDual u
    let K:=seccionDelDual u i
    (∫ s,energiaEnSeccion a K (campoDual u i) s ∂marginalRef i)≤∫ s,energiaEnSeccion a K w s ∂marginalRef i := by
  obtain ⟨v,other,cost,Z⟩:=competidor_de_una_linea hp u i wm wb
  have action:=mayorante_tangente_en_el_minimo hp dp u minimal v
  have cancel : (∑ j,costoDual u j)-(∑ j,costoDual v j)=costoDual u i-costoDual v i := by
    rw [←Finset.sum_sub_distrib]; apply Finset.sum_eq_single i
    · intro j _ ne; rw [other j ne,sub_self]
    · simp
  have eq := partida_con_un_potencial u i (campo_dual_medible u) (campo_dual_acotado hp u) u
    (fun _=>EventuallyEq.rfl) (fun _ _=>rfl)
  let a:=d/particionDual u
  change (∑ j,costoDual u j)+a*particionDual u≤(∑ j,costoDual v j)+a*particionDual v at action
  rw [eq,Z] at action
  rw [cost] at cancel
  change (∫ s,energiaEnSeccion a _ _ s ∂marginalRef i)≤∫ s,energiaEnSeccion a _ _ s ∂marginalRef i
  rw [(energia_de_seccion_integrable hp u i (a:=a) (campo_dual_medible u i) (campo_dual_acotado hp u i)).2,
    (energia_de_seccion_integrable hp u i (a:=a) wm wb).2]
  change costoDual u i+_≤_
  linarith only [cancel,action]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.energia_de_seccion_integrable
#print axioms ArticuloA.Historias.energia_de_seccion_minima
