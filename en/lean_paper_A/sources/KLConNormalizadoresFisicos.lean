import EntropiaDelNucleoFisico
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}
def costeNormalizadores (n q : ℕ) (base : Fin 4 → Indice n → ℝ)
    (D : Historia n q → Indice n → ℝ) : ℝ :=
  (∑ H : Historia n q,proba n q * ∑ t,Real.log (D H t)) -
  (∑ i,∑ j,Real.log (base i j)) - Real.log (count n q) -
    Real.log q.factorial - 4*Real.log (2*n-1-q).factorial

theorem kl_real_y_virtual (h : ℕ) (level : q=n-h) (hn : 0<count n q)
    (u : Fin 4 → ℕ → ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) :
    let d:=costeNormalizadores n q (factores u) (fun H => normalizador H (factores u))
    Real.exp (-d) ≤ exitoE2 n h (sameColors u) ∧ KLcondicionado n q h (sameColors u) ≤ d := by
  let v := fun H : Historia n q => masaRamaCon H (factores u) (fun J => normalizador J (factores u))
  have pos (H : Historia n q) : 0<v H := masaRamaCon_pos _ (fun J t => positivo J _ hu t) H _ hu
  have den (H : Historia n q) (i : Indice n) : denominador (estado H h i.val) (sameColors u) (secuencia H i)≠0 := by
    intro zero
    have wz := masa_comun H h u i
    rw [zero] at wz
    exact (positivo H _ hu i).ne' wz.symm
  have X := transferencia_de_las_ramas h level hn (sameColors u) v pos (fun H => peso_fisico_comun H h level u) den
  have eq : costeRamas v=costeNormalizadores n q (factores u) (fun H => normalizador H (factores u)) :=
    identidad_entropica _ hu hn
  simpa only [eq] using X

theorem kl_tablero_lleno (hn : 0<count n n) (u : Fin 4 → ℕ → ℝ≥0)
    (hu : ∀ i j,0<factores (n:=n) u i j) :
    let d:=costeNormalizadores n n (efectivos (factores u)) (fun H => normalizadorCero H (factores u))
    Real.exp (-d) ≤ exitoE2 n 0 (coloresLlenos n u) ∧ KLcondicionado n n 0 (coloresLlenos n u) ≤ d := by
  let v := fun H : Historia n n => ramaCero H (factores u)
  have pos (H : Historia n n) : 0<v H := by
    have eq : v H=masaRamaCon H (efectivos (factores u)) (fun J => normalizadorCero J (factores u)) := by
      dsimp only [v,ramaCero,masaRamaCon]; simp_rw [peso_sobre_el_soporte]
    exact eq ▸ masaRamaCon_pos _ (fun J t => normalizadorCero_pos J _ hu t) H _ (efectivos_pos _ hu)
  have den (H : Historia n n) (i : Indice n) :
      denominador (estado H 0 i.val) (coloresLlenos n u) (secuencia H i)≠0 := by
    intro zero
    have wz := masa_en_lleno H u i
    rw [zero] at wz
    exact (normalizadorCero_pos H _ hu i).ne' wz.symm
  have X := transferencia_de_las_ramas 0 (by omega) hn (coloresLlenos n u) v pos (fun H => peso_fisico_en_lleno H u) den
  have eq : costeRamas v=costeNormalizadores n n (efectivos (factores u)) (fun H => normalizadorCero H (factores u)) :=
    identidad_nivel_cero _ hu hn
  simpa only [eq] using X
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.kl_real_y_virtual
#print axioms ArticuloA.Historias.kl_tablero_lleno
