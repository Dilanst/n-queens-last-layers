import BalanceUniformeParaElNumeroDeHuecosVariable
namespace ArticuloA.Historias
open Perfil Real Filter
open scoped BigOperators NNReal
noncomputable section

theorem resto_relativo_de_una_holgura {u v d : ℝ} (up : 0<u) (vp : 0<v)
    (ratio : v≤2*u) (dif : |v-u|≤d) : v*(log v-log u)≤2*d := by
  have dn:0≤d:=(abs_nonneg _).trans dif
  by_cases small : v≤u
  · exact (mul_nonpos_of_nonneg_of_nonpos vp.le (sub_nonpos.mpr (log_le_log vp small))).trans (by positivity)
  have diff:=log_sobre_referencia v u vp up
  have lg:0≤log v-log u:=sub_nonneg.mpr (log_le_log up (le_of_not_ge small))
  calc
    _ ≤ (2*u)*(log v-log u) := mul_le_mul_of_nonneg_right ratio lg
    _ = 2*(u*(log v-log u)) := by ring
    _ ≤ 2*d := by linarith only [diff,(abs_le.mp dif).2]

/-- The total error is controlled even when the transversal slacks tend to zero. -/
theorem resto_total_de_holguras_muestreadas {n : ℕ} {h : ℕ} {p : FactoresContinuos}
    (hn : 0<n) (C : ℝ) (cp : 0≤C)
    (fits : ∀ i (j : Indice n),
      let u:=holguraInicial n h p i j
      let v:=1-cargaLinea n (n-h) p i j
      0<u ∧ 0<v ∧ v≤2*u ∧ |v-u|≤C/n) :
    (∑ i,∑ j : Indice n,(1-cargaLinea n (n-h) p i j)*
      (log (1-cargaLinea n (n-h) p i j)-log (holguraInicial n h p i j)))≤16*C := by
  have nr : 0<(n:ℝ):=by exact_mod_cast hn
  have two : ((2*n-1:ℕ):ℝ)≤2*n:=by exact_mod_cast (show 2*n-1≤2*n by omega)
  have single (i : Fin 4) (j : Indice n) := resto_relativo_de_una_holgura
    (fits i j).1 (fits i j).2.1 (fits i j).2.2.1 (fits i j).2.2.2
  calc
    _ ≤ ∑ _i : Fin 4,∑ _j : Indice n,2*(C/n) := Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>single i j))
    _ = 4*(((2*n-1:ℕ):ℝ)*(2*(C/n))) := by simp [Indice,nsmul_eq_mul]
    _ ≤ 4*((2*n:ℝ)*(2*(C/n))) := by gcongr
    _ = 16*C := by field_simp; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.resto_total_de_holguras_muestreadas
