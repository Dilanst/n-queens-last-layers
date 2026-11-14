import CuadraturaDelTablero
import SumasDeUnaFamilia
import ErroresLogaritmicosDeMasa
open MeasureTheory Set
open scoped BigOperators Interval NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section
open Classical

def intervaloLog (a b : ℝ) (f : ℝ→ℝ≥0) := ∫ t in a..b,Real.log (f t)
def entropiaDeFactores (p : FactoresContinuos) (x : ℝ≥0) :=
  2*Real.log x+intervaloLog 0 1 p.fila+intervaloLog 0 1 p.columna+
    intervaloLog (-1) 1 p.diagonal+intervaloLog 0 2 p.anti

structure RegularEn (I : Set ℝ) (f : ℝ→ℝ≥0) (κ L : ℝ) : Prop where
  minimo : ∀ x∈I, κ≤f x
  oscilacion : ∀ x∈I,∀ y∈I,|(f x:ℝ)-f y|≤L*|x-y|

theorem RegularEn.logarithmos {I f κ L} (data : RegularEn I f κ L) (kp : 0<κ) :
    ∀ x∈I,∀ y∈I,|Real.log (f x)-Real.log (f y)|≤(L/κ)*|x-y| := by
  intro x hx y hy
  simpa only [div_mul_eq_mul_div] using lipschitz_del_log kp (data.minimo x hx) (data.minimo y hy)
    (data.oscilacion x hx y hy)

theorem log_en_transversal (n : ℕ) (hn : 0<n) (f : ℝ→ℝ≥0) (κ L : ℝ) (kp : 0<κ) (lp : 0≤L)
    (reg : RegularEn unidadCerrada f κ L) :
    |(n:ℝ)*intervaloLog 0 1 f-familiaReal n (fun x => Real.log (f x))|≤L/κ := by
  have h:=reg.logarithmos kp
  have q := cuadratura_centros n hn _ _ (div_nonneg lp kp.le) (continua_de_cota (div_nonneg lp kp.le) h) h
  simpa only [intervaloLog,familiaReal,centro,nodo,zero_add,medio] using q

theorem log_en_diagonal (n : ℕ) (hn : 0<n) (a : ℝ) (f : ℝ→ℝ≥0) (κ L : ℝ) (kp : 0<κ) (lp : 0≤L)
    (reg : RegularEn (Icc a (a+2)) f κ L) (extremo : f a=1) :
    |(n:ℝ)*intervaloLog a (a+2) f-familiaOblicua n a (fun x => Real.log (f x))|≤2*(L/κ) := by
  have h := reg.logarithmos kp
  have q := cuadratura_diagonales n hn a _ _ (div_nonneg lp kp.le) (continua_de_cota (div_nonneg lp kp.le) h) h
  simpa only [intervaloLog,familiaOblicua,Perfil.interior,nodo,oblicuo,Nat.cast_add,Nat.cast_one,add_zero,
    extremo,NNReal.coe_one,Real.log_one,abs_zero] using q

theorem error_del_producto_de_pesos (n : ℕ) (hn : 0<n) (p : FactoresContinuos) (x : ℝ≥0) (xp : 0<x)
    (κ L : ℝ) (kp : 0<κ) (lp : 0≤L)
    (row : RegularEn unidadCerrada p.fila κ L) (col : RegularEn unidadCerrada p.columna κ L)
    (diag : RegularEn (Icc (-1) 1) p.diagonal κ L) (anti : RegularEn (Icc 0 2) p.anti κ L)
    (de : p.diagonal (-1)=1) (ae : p.anti 0=1) :
    |(n:ℝ)*entropiaDeFactores p x-(∑ i,∑ j : Indice n,Real.log (factores (pesosMalla n x p) i j))|≤6*(L/κ) := by
  have r:=log_en_transversal n hn _ _ _ kp lp row
  have c:=log_en_transversal n hn _ _ _ kp lp col
  have d:=log_en_diagonal n hn (-1) _ _ _ kp lp (by norm_num; exact diag) de
  have a:=log_en_diagonal n hn 0 _ _ _ kp lp (by simpa using anti) ae
  norm_num at d a
  have rp (i : ℕ) (hi : i<n) : 0<p.fila (medio n i) := by
    exact_mod_cast kp.trans_le (row.minimo _ (by simpa [centro,nodo,medio] using centro_pertenece n i hi))
  have cp (i : ℕ) (hi : i<n) : 0<p.columna (medio n i) := by
    exact_mod_cast kp.trans_le (col.minimo _ (by simpa [centro,nodo,medio] using centro_pertenece n i hi))
  rw [suma_de_log_malla n hn x xp p rp cp]
  unfold entropiaDeFactores
  rw [abs_le] at r c d a ⊢
  constructor <;> linarith only [r.1,r.2,c.1,c.2,d.1,d.2,a.1,a.2]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_del_producto_de_pesos
