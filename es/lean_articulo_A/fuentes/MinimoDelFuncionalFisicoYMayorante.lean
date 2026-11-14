import ContinuidadDelFuncionalDual
import BrechaDelFuncionalDualMedido
import CoercividadYEscalaDelDual
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section

theorem minimo_unico_del_funcional_fisico {H d : ℝ} (hp : 0≤H) (dp : 0<d) (dt : d<1) :
    ∃! u : CajaDual H,∀ v : CajaDual H,funcionalDual d u≤funcionalDual d v := by
  classical
  letI : CompleteSpace (CajaDual H):=caja_de_potenciales_completa hp
  letI : Nonempty (CajaDual H):=⟨⟨0,cero_pertenece_a_la_caja hp⟩⟩
  have low : BddBelow (range (funcionalDual (H:=H) d)) := by
    refine ⟨-6,?_⟩
    rintro y ⟨u,rfl⟩
    have pos : 0≤masaDePotenciales u := Finset.sum_nonneg (fun i _=>integral_nonneg (fun s=>(campo_dual_acotado hp u i s).1))
    have b:=cota_inferior_funcional hp dp.le u
    linarith only [mul_nonneg (sub_nonneg.mpr dt.le) pos,b]
  let mid (u v : CajaDual H):=(promedio_en_la_caja hp u v).choose
  exact minimo_unico_por_brecha_de_punto_medio _ mid (funcional_dual_continuo hp d) low
    (div_pos (by norm_num : (0:ℝ)<8) (exp_pos (-H)))
    (fun u v=>brecha_del_funcional_dual hp dp.le u v (mid u v) (promedio_en_la_caja hp u v).choose_spec)

theorem mayorante_tangente_en_el_minimo {H d : ℝ} (hp : 0≤H) (dp : 0<d) (u : CajaDual H)
    (minimal : ∀ v : CajaDual H,funcionalDual d u≤funcionalDual d v) (v : CajaDual H) :
    (∑ i,costoDual u i)+(d/particionDual u)*particionDual u ≤
      (∑ i,costoDual v i)+(d/particionDual u)*particionDual v := by
  have pos (w : CajaDual H) : 0<particionDual w := (exp_pos _).trans_le (particion_dual_acotada hp w).1
  have l:=Real.log_le_sub_one_of_pos (div_pos (pos v) (pos u))
  rw [log_div (pos v).ne' (pos u).ne'] at l
  have cap:=mul_le_mul_of_nonneg_left l dp.le
  have h:=minimal v
  unfold funcionalDual at h
  have den : d/particionDual u*particionDual u=d := div_mul_cancel₀ _ (pos u).ne'
  rw [den]; rw [show d/particionDual u*particionDual v=d*(particionDual v/particionDual u) by ring]
  linarith only [cap,h]

theorem ecuacion_puntual_del_mayorante {A : ℝ} (ap : 0<A) (v : ℝ) :
    log A + A*exp (-log A)≤v+A*exp (-v) ∧
    (log A+A*exp (-log A)=v+A*exp (-v) → v=log A) := by
  have one : A*exp (-log A)=1 := by rw [exp_neg,exp_log ap,mul_inv_cancel₀ ap.ne']
  have factor : A*exp (-v)=exp (log A-v) := by rw [sub_eq_add_neg,exp_add,exp_log ap]
  rw [one,factor]
  constructor
  · linarith only [add_one_le_exp (log A-v)]
  · intro eq; by_contra ne
    have strict:=Real.add_one_lt_exp (show log A-v≠0 from sub_ne_zero.mpr (Ne.symm ne))
    linarith only [strict,eq]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.minimo_unico_del_funcional_fisico
#print axioms ArticuloA.Historias.mayorante_tangente_en_el_minimo
#print axioms ArticuloA.Historias.ecuacion_puntual_del_mayorante
