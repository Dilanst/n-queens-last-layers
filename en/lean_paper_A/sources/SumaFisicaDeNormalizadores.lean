import PresupuestosFisicosDelRango
import PromedioDelOrdenFisico
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita Revelado
noncomputable section
open Classical
variable {n q : ℕ}

def masaSegun (P : Tablero n q) (C : Completion P) (u : ColorWeights NNReal)
    (p : Indice n) (T : Finset (Indice n)) :=
  match pieza P C p with
  | .real _ => porSubconjunto Finset.univ (fun e : Cell n => otros P C p (tuplaReal e))
      (fun e => pesoDe (factores u.real) (tuplaReal e)) T
  | .virtual _ => porSubconjunto Finset.univ (otros P C p) (pesoDe (factores u.virtual)) T

theorem denominador_segun (H : Historia n q) (h : ℕ) (t : Indice n) (u : ColorWeights NNReal) :
    (denominador (estado H h t.val) u (secuencia H t)).val =
      masaSegun H.1 H.2.1 u (H.2.2 t) (posteriores H t) := by
  unfold masaSegun
  change _ = match secuencia H t with
    | .real _ => _
    | .virtual _ => _
  cases ht : secuencia H t with
  | real _ =>
    rw [denominador,normalizador_real]
    simp_rw [disponibleEn,disponible]
    rfl
  | virtual _ =>
    rw [denominador,normalizador_virtual]
    simp_rw [disponibleEn,disponible]
    rfl

/-- This expectation is taken over the orders of one fixed completed matching. -/
theorem aplicar_rangos_al_nucleo (P : Tablero n q) (C : Completion P) (h : ℕ)
    (u : ColorWeights NNReal) (b : Indice n → ℝ)
    (cap : ∀ p, (∑ m∈Finset.range (2*n-1),
      porRango (Finset.univ.erase p) m (fun T => Real.log (masaSegun P C u p T)))≤b p) :
    (∑ s : Equiv.Perm (Indice n), ∑ t : Indice n,
      Real.log ((denominador (estado (⟨P,C,s⟩ : Historia n q) h t.val) u
        (secuencia (⟨P,C,s⟩ : Historia n q) t)).val))/(2*n-1).factorial ≤ (∑ p,b p)/(2*n-1:ℕ) := by
  simp_rw [denominador_segun]
  exact cota_del_orden (fun p T => Real.log (masaSegun P C u p T)) b cap
/-- A concrete cap for the previous inequality, for either color of a marked piece. -/
theorem rango_fisico_con_difusion {β : Type} [Fintype β] (P : Tablero n q) (C : Completion P)
    (p : Indice n) (a : β→Candidata n) (inj : Function.Injective a) (j : ℕ) (j1 : 1≤j)
    (w : β→ℝ) (nn : ∀ e,0≤w e) (W M A : ℝ) (W0 : 0<W) (M0 : 0≤M) (A0 : 0≤A)
    (total : ∑ e,w e=W) (cap : ∀ e,w e≤M)
    (diff : M*(↑(2*n-1):ℝ)^(j+1)≤A*W)
    (bound : (Finset.univ.filter (fun e : β => (otros P C p (a e)).card≠4)).card≤10*(2*n-1)^j)
    (marked : ∃ e,otros P C p (a e)=∅ ∧ 0<w e)
    (D : 0<(Finset.univ.erase p).card) :
    let U:=Finset.univ.erase p
    (∑ m∈Finset.range (2*n-1),porRango U m
      (fun T => Real.log (porSubconjunto Finset.univ (fun e => otros P C p (a e)) w T))) ≤
      (↑(2*n-1):ℝ)*Real.log W-4*(↑(2*n-1):ℝ)+4+(4+6*(10*A))*(Rangos.corte U.card D:ℝ) := by
  let U:=Finset.univ.erase p
  have sz : U.card+1=2*n-1 := by
    have nz := p.isLt
    dsimp only [U]; rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin]; omega
  have eq : (U.card:ℝ)+1=(↑(2*n-1):ℝ) := by exact_mod_cast sz
  have pr := escala_fisica P C p a inj (2*n-1) j (by have := p.isLt; omega) j1 w W M A M0 cap diff bound
  have ex : (∑ e,if (otros P C p (a e)).card≠4 then w e else 0)≤(10*A)*W/((U.card:ℝ)+1) := by
    rw [eq]; exact pr.1
  have sp : (∑ e,if otros P C p (a e)=∅ then w e else 0)≤(10*A)*W/((U.card:ℝ)+1)^2 := by
    rw [eq]
    apply pr.2.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith : A≤10*A) W0.le
  obtain ⟨e,empty,positive⟩ := marked
  have result := suma_de_log_por_pieza U Finset.univ (fun e => otros P C p (a e))
    (fun e _ => todos_distintos_de P C p (a e)) w (fun e _ => nn e) W0 (by positivity : 0≤10*A)
    D total ex sp ⟨e,Finset.mem_univ e,empty,positive⟩
  dsimp only
  rw [sz,eq] at result
  exact result
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.rango_fisico_con_difusion
#print axioms ArticuloA.Historias.denominador_segun
#print axioms ArticuloA.Historias.aplicar_rangos_al_nucleo
