import MediaDeLasCompletaciones
import KLConNormalizadoresFisicos
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita Revelado
noncomputable section
open Classical
variable {n q : ℕ}

def constanteDifusion (bR BR bV BV : ℝ) := max (4*BR/bR) (9*BV/bV^4)

def desde_cotas_de_factores (hn : 2≤n) (u : ColorWeights ℝ≥0) (x bR BR bV BV : ℝ)
    (x0 : 0<x) (r0 : 0<bR) (R0 : 0≤BR) (v0 : 0<bV) (V0 : 0≤BV)
    (realInf : ∀ e : Cell n,bR*x^2≤wCelda u e) (realSup : ∀ e : Cell n,wCelda u e≤BR*x^2)
    (virtualSup : ∀ a : Candidata n,wTupla u a≤BV)
    (fila : ∀ j : Indice n,n ≤ j.val → bV≤factores u.virtual 0 j)
    (col : ∀ j : Indice n,n ≤ j.val → bV≤factores u.virtual 1 j)
    (diag : ∀ j : Indice n,bV≤factores u.virtual 2 j) (anti : ∀ j : Indice n,bV≤factores u.virtual 3 j) :
    Difusos n u (constanteDifusion bR BR bV BV) := by
  have npos : (0:ℝ)<(2*n-1:ℕ) := by exact_mod_cast (by omega : 0<2*n-1)
  haveI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  have rpos : 0<Wreal n u := Finset.sum_pos (fun e _ => (mul_pos r0 (sq_pos_of_pos x0)).trans_le (realInf e)) Finset.univ_nonempty
  have vv := difusion_virtual_inicial hn (factores u.virtual) bV 1 v0 zero_le_one
    (fun _ _ => NNReal.coe_nonneg _) fila col diag anti
  have vpos : 0<Wvirtual n u := by
    by_contra! bad
    have neg := mul_nonpos_of_nonneg_of_nonpos (show (0:ℝ)≤9*1/bV^4 by positivity) bad
    have pos := pow_pos npos 4; exact (not_lt_of_ge (vv.trans neg)) (by simpa only [one_mul] using pos)
  refine ⟨BR*x^2,BV,(show 0≤4*BR/bR by positivity).trans (le_max_left _ _),by positivity,V0,
    rpos,vpos,realSup,virtualSup,?_,?_⟩
  · exact (difusion_real_inicial (wCelda u) x bR BR r0 R0 realInf).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) rpos.le)
  · exact (difusion_virtual_inicial hn (factores u.virtual) bV BV v0 V0
      (fun _ _ => NNReal.coe_nonneg _) fila col diag anti).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) vpos.le)

theorem elegida_comun_positiva (P : Tablero n q) (C : Completion P) (p : Indice n)
    (u : Fin 4→ℕ→ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) :
    0<(elegido (sameColors u) (pieza P C p)).val := by
  let H : Historia n q := ⟨P,C,Equiv.refl _⟩
  change 0<(elegido _ (secuencia H p)).val
  rw [peso_comun]
  unfold peso pesoDe
  exact Finset.prod_pos (fun i _ => hu i _)

theorem elegida_llena_positiva (P : Tablero n n) (C : Completion P) (p : Indice n)
    (u : Fin 4→ℕ→ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) :
    0<(elegido (coloresLlenos n u) (pieza P C p)).val := by
  let H : Historia n n := ⟨P,C,Equiv.refl _⟩
  change 0<(elegido _ (secuencia H p)).val
  rw [peso_en_lleno,peso_sobre_el_soporte]
  unfold peso pesoDe
  exact Finset.prod_pos (fun i _ => efectivos_pos _ hu i _)

def cotaKL (n q : ℕ) (hn : 2≤n) (u : ColorWeights ℝ≥0) (A : ℝ) (base : Fin 4→Indice n→ℝ) :=
  cotaMedia n q hn u A-(∑ i,∑ j,Real.log (base i j))-Real.log (count n q)-
    Real.log q.factorial-4*Real.log (2*n-1-q).factorial

private theorem transferir_cota {a b s D : ℝ} (ab : a≤b)
    (both : Real.exp (-a)≤s ∧ D≤a) : Real.exp (-b)≤s ∧ D≤b :=
  ⟨(Real.exp_le_exp.mpr (neg_le_neg ab)).trans both.1,both.2.trans ab⟩

theorem comparacion_con_masas (hn : 2≤n) (h : ℕ) (lev : q=n-h) (counted : 0<count n q)
    (u : Fin 4→ℕ→ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) (A : ℝ) (dif : Difusos n (sameColors u) A) :
    let b:=cotaKL n q hn (sameColors u) A (factores u)
    Real.exp (-b)≤exitoE2 n h (sameColors u) ∧ KLcondicionado n q h (sameColors u)≤b := by
  have ub := media_en_historias h hn counted _ A dif (fun P C p => elegida_comun_positiva P C p u hu)
  simp only [costeLog,masa_comun] at ub
  apply transferir_cota _ (kl_real_y_virtual h lev counted u hu)
  dsimp only [costeNormalizadores,cotaKL]; linarith only [ub]

theorem comparacion_llena_con_masas (hn : 2≤n) (counted : 0<count n n)
    (u : Fin 4→ℕ→ℝ≥0) (hu : ∀ i j,0<factores (n:=n) u i j) (A : ℝ) (dif : Difusos n (coloresLlenos n u) A) :
    let b:=cotaKL n n hn (coloresLlenos n u) A (efectivos (factores u))
    Real.exp (-b)≤exitoE2 n 0 (coloresLlenos n u) ∧ KLcondicionado n n 0 (coloresLlenos n u)≤b := by
  have ub := media_en_historias 0 hn counted _ A dif (fun P C p => elegida_llena_positiva P C p u hu)
  simp only [costeLog,masa_en_lleno] at ub
  apply transferir_cota _ (kl_tablero_lleno counted u hu)
  dsimp only [costeNormalizadores,cotaKL]; linarith only [ub]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.desde_cotas_de_factores
#print axioms ArticuloA.Historias.comparacion_con_masas
#print axioms ArticuloA.Historias.comparacion_llena_con_masas
