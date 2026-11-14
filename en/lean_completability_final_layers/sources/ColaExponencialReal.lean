import MomentoDeInnovaciones
import Mathlib.Data.Complex.Exponential
namespace ArticuloA.RealFinita
noncomputable def realExp : Momento.Exponencial where
  fn := Real.exp
  zero := Real.exp_zero
  add := Real.exp_add
  pos := Real.exp_pos
  mono := fun _ _ => Real.exp_le_exp.mpr
  arriba := Real.add_one_le_exp
  cuadratico := fun hx => (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hx)
abbrev mgf_fila {X : Type} := @Momento.mgf_fila realExp X
abbrev cola {X : Type} := @Momento.cola realExp X
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.cola
