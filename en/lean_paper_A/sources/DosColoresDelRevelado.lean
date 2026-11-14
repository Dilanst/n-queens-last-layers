import NormalizadoresDeE2
import PesosDeLosDosColores
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}

def elegido (u : ColorWeights ℝ≥0) : Pieza n → ℝ≥0
  | .real e => weights masas u.real (lines e)
  | .virtual g => weights masas u.virtual g

def denominador (x : State n) (u : ColorWeights ℝ≥0) : Pieza n → ℝ≥0
  | .real _ => total masas (realChoices masas x u)
  | .virtual _ => total masas (virtualChoices masas x u.virtual)

theorem peso_comun (H : Historia n q) (u : Fin 4 → ℕ → ℝ≥0) (t : Indice n) :
    (elegido (sameColors u) (secuencia H t)).val=peso H (factores u) t := by
  have eq := cuatro_pesos u (tupla H t)
  change (weights masas u (edgeOf (secuencia H t))).val = _ at eq
  cases ht : secuencia H t <;> simpa only [ht,elegido,sameColors] using eq

theorem masa_comun (H : Historia n q) (h : ℕ) (u : Fin 4 → ℕ → ℝ≥0) (t : Indice n) :
    (denominador (estado H h t.val) (sameColors u) (secuencia H t)).val =
      normalizador H (factores u) t := by
  cases ht : secuencia H t with
  | real _ => simpa only [normalizador,ht,denominador,sameColors] using normalizador_real H h t (sameColors u)
  | virtual _ => simpa only [normalizador,ht,denominador,sameColors] using normalizador_virtual H h t (sameColors u)

def coloresLlenos (n : ℕ) (u : Fin 4 → ℕ → ℝ≥0) := fullColors masas n (u 0) (u 1) (u 2) (u 3)

theorem real_lleno (u : Fin 4 → ℕ → ℝ≥0) (e : Cell n) :
    pesoDe (factores (coloresLlenos n u).real) (tuplaReal e)=pesoDe (efectivos (factores u)) (tuplaReal e) := by
  apply Finset.prod_congr rfl
  intro i _
  fin_cases i <;> simp [factores,coloresLlenos,fullColors,efectivos,tuplaReal,lines,not_le.mpr e.1.isLt,not_le.mpr e.2.isLt]

theorem virtual_lleno (u : Fin 4 → ℕ → ℝ≥0) (a : Candidata n) :
    pesoDe (factores (coloresLlenos n u).virtual) a = pesoVirtualCero (factores u) a := by
  rw [←cuatro_pesos]
  unfold coloresLlenos
  rw [full_virtual]
  unfold pesoVirtualCero pesoDe
  rw [Fin.prod_univ_four]
  change (↑(if (a 0).val<n ∨ (a 1).val<n then (0:ℝ≥0) else u 2 (a 2).val*u 3 (a 3).val):ℝ) = _
  by_cases r : n≤(a 0).val <;> by_cases c : n≤(a 1).val <;>
    simp [r,c,show (a 0).val<n ↔ ¬n≤(a 0).val by omega,show (a 1).val<n ↔ ¬n≤(a 1).val by omega,
      efectivos,factores,show ¬(3:Fin 4).val<2 by decide]

theorem peso_en_lleno (H : Historia n n) (u : Fin 4 → ℕ → ℝ≥0) (t : Indice n) :
    (elegido (coloresLlenos n u) (secuencia H t)).val = pesoElegido H (factores u) t := by
  cases eq : secuencia H t with
  | real e =>
    have same : tuplaReal e=tupla H t := by
      funext i; apply Fin.ext; exact (congrArg (fun v => edgeOf v i) eq).symm
    rw [pesoElegido,eq]
    change (weights masas _ (numeros (tuplaReal e))).val=pesoDe _ _
    rw [cuatro_pesos,real_lleno,same]
  | virtual g =>
    have same : numeros (tupla H t)=g := congrArg edgeOf eq
    rw [pesoElegido,eq]
    change (weights masas _ g).val=_
    rw [←same,cuatro_pesos,virtual_lleno]

theorem masa_en_lleno (H : Historia n n) (u : Fin 4 → ℕ → ℝ≥0) (t : Indice n) :
    (denominador (estado H 0 t.val) (coloresLlenos n u) (secuencia H t)).val =
      normalizadorCero H (factores u) t := by
  cases ht : secuencia H t with
  | real _ =>
    rw [normalizadorCero,ht,normalizador,ht]
    change (total masas (realChoices masas _ _)).val=_
    rw [normalizador_real]; simp_rw [real_lleno]
  | virtual _ =>
    rw [normalizadorCero,ht]
    change (total masas (virtualChoices masas _ _)).val=_
    rw [normalizador_virtual]; simp_rw [virtual_lleno]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_comun
#print axioms ArticuloA.Historias.masa_en_lleno
#print axioms ArticuloA.Historias.peso_en_lleno
