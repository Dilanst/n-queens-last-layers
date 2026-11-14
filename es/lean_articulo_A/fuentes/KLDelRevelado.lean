import ComparacionFinitaDelPerfil
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}
def masaTraza (n h : ℕ) (u : ColorWeights ℝ≥0) (l : List (Choice n)) :=
  (avg masas (arbol u (2*n-1) (initial n h)) (fun y => if y.1=l then 1 else 0)).val
def KLtrazas (n q h : ℕ) (u : ColorWeights ℝ≥0) :=
  ∑ H : Historia n q,proba n q*Real.log (proba n q/masaTraza n h u (etiquetas H))

theorem rama_dominada_por_traza (H : Historia n q) (h : ℕ) (lev : q=n-h) (u : ColorWeights ℝ≥0)
    (nz : ∀ i,denominador (estado H h i.val) u (secuencia H i)≠0) :
    (pesoCamino H h u).val≤masaTraza n h u (etiquetas H) := by
  let y : Registro n := (etiquetas H,estado H h (2*n-1))
  have a := suma_de_atomos (arbol u (2*n-1) (initial n h)) (fun _ : Unit => pesoCamino H h u)
    (fun _ : Unit => y) (fun _ _ _ => Subsingleton.elim _ _) (fun _ => camino_completo H h lev u nz)
    (fun z => if z.1=etiquetas H then 1 else 0) (fun _ => if_pos rfl)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_unit,one_nsmul,masaTraza] using a

theorem trazas_por_ramas (h : ℕ) (lev : q=n-h) (cnt : 0<count n q) (u : ColorWeights ℝ≥0)
    (v : Historia n q→ℝ) (vp : ∀ H,0<v H) (peso : ∀ H,(pesoCamino H h u).val=v H)
    (nz : ∀ (H : Historia n q) i,denominador (estado H h i.val) u (secuencia H i)≠0) :
    KLtrazas n q h u≤costeRamas v := by
  have pr : 0<proba n q := by rw [proba,card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]; positivity
  apply Finset.sum_le_sum; intro H _
  have dom := rama_dominada_por_traza H h lev u (nz H); rw [peso H] at dom
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos pr ((vp H).trans_le dom))
    (div_le_div_of_nonneg_left pr.le (vp H) dom)) pr.le

theorem tres_cotas_comunes (hn : 2≤n) (h : ℕ) (lev : q=n-h) (cnt : 0<count n q)
    (u : Fin 4→ℕ→ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) (A : ℝ) (dif : Difusos n (sameColors u) A) :
    let b:=cotaKL n q hn (sameColors u) A (factores u)
    KLtrazas n q h (sameColors u)≤b ∧ Real.exp (-b)≤exitoE2 n h (sameColors u) ∧ KLcondicionado n q h (sameColors u)≤b := by
  refine ⟨?_,comparacion_con_masas hn h lev cnt u hu A dif⟩
  let v := fun H : Historia n q => masaRamaCon H (factores u) (fun J => normalizador J (factores u))
  have pos (H : Historia n q) : 0<v H := masaRamaCon_pos _ (fun J t => positivo J _ hu t) H _ hu
  have nz (H : Historia n q) (i : Indice n) : denominador (estado H h i.val) (sameColors u) (secuencia H i)≠0 := by
    intro bad; have e := masa_comun H h u i; rw [bad] at e; exact (positivo H _ hu i).ne' e.symm
  apply (trazas_por_ramas h lev cnt _ v pos (fun H => peso_fisico_comun H h lev u) nz).trans
  have eq : costeRamas v = costeNormalizadores n q (factores u) (fun H => normalizador H (factores u)) := identidad_entropica _ hu cnt
  have ub := media_en_historias h hn cnt _ A dif (fun P C p => elegida_comun_positiva P C p u hu)
  simp only [costeLog,masa_comun] at ub
  rw [eq]; dsimp only [costeNormalizadores,cotaKL]; linarith only [ub]

theorem tres_cotas_en_lleno (hn : 2≤n) (cnt : 0<count n n) (u : Fin 4→ℕ→ℝ≥0)
    (hu : ∀ i j,0<factores (n:=n) u i j) (A : ℝ) (dif : Difusos n (coloresLlenos n u) A) :
    let b:=cotaKL n n hn (coloresLlenos n u) A (efectivos (factores u))
    KLtrazas n n 0 (coloresLlenos n u)≤b ∧ Real.exp (-b)≤exitoE2 n 0 (coloresLlenos n u) ∧ KLcondicionado n n 0 (coloresLlenos n u)≤b := by
  refine ⟨?_,comparacion_llena_con_masas hn cnt u hu A dif⟩
  let v := fun H : Historia n n => ramaCero H (factores u)
  have pos (H : Historia n n) : 0<v H := by
    have eq : v H=masaRamaCon H (efectivos (factores u)) (fun J => normalizadorCero J (factores u)) := by
      dsimp only [v,ramaCero,masaRamaCon]; simp_rw [peso_sobre_el_soporte]
    rw [eq]
    exact masaRamaCon_pos _ (fun J t => normalizadorCero_pos J _ hu t) H _ (efectivos_pos _ hu)
  have nz (H : Historia n n) (i : Indice n) : denominador (estado H 0 i.val) (coloresLlenos n u) (secuencia H i)≠0 := by
    intro bad; have e := masa_en_lleno H u i; rw [bad] at e; exact (normalizadorCero_pos H _ hu i).ne' e.symm
  apply (trazas_por_ramas 0 (by omega) cnt _ v pos (fun H => peso_fisico_en_lleno H u) nz).trans
  have eq : costeRamas v = costeNormalizadores n n (efectivos (factores u)) (fun H => normalizadorCero H (factores u)) := identidad_nivel_cero _ hu cnt
  have ub := media_en_historias 0 hn cnt _ A dif (fun P C p => elegida_llena_positiva P C p u hu)
  simp only [costeLog,masa_en_lleno] at ub
  rw [eq]; dsimp only [costeNormalizadores,cotaKL]; linarith only [ub]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tres_cotas_comunes
#print axioms ArticuloA.Historias.tres_cotas_en_lleno
