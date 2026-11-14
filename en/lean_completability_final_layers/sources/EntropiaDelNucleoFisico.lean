import PesoDeLaHistoriaEnE2
import EntropiaProyectadaAlTablero
import EntropiaCondicionadaAlExito
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita
noncomputable section
open Classical
variable {n q : ℕ}
def esExito (x : State n) : Prop := x.failed=false ∧ x.reals=0 ∧ x.virtuals=0
def terminalE2 (n h : ℕ) (u : ColorWeights ℝ≥0) := leaves masas (kernel masas u (·⁻¹)) 0 (2*n-1) (initial n h)
def exitoE2 (n h : ℕ) (u : ColorWeights ℝ≥0) :=
  (avg masas (terminalE2 n h u) (fun x => if esExito x then 1 else 0)).val
def masaTablero (P : Tablero n q) (h : ℕ) (u : ColorWeights ℝ≥0) :=
  (avg masas (terminalE2 n h u) (indicadorExitoso P.val)).val
def costeRamas (v : Historia n q → ℝ) := ∑ H, proba n q*Real.log (proba n q/v H)
def KLcondicionado (n q h : ℕ) (u : ColorWeights ℝ≥0) := ∑ P : Tablero n q,
  (count n q:ℝ)⁻¹*Real.log ((count n q:ℝ)⁻¹/(masaTablero P h u/exitoE2 n h u))

private theorem exito_maximo (n h : ℕ) (u : ColorWeights ℝ≥0) : exitoE2 n h u≤1 := by
  let L:=terminalE2 n h u
  have pos (i j : ℕ) (nz : i+j≠0) : masas.add (masas.times i masas.one) (masas.times j masas.one)≠masas.zero := by
    change E2.Regular.ns masas i+E2.Regular.ns masas j≠0
    rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast nz
  have one : total masas L=1 := law_one masas u (·⁻¹) (fun a ne => inv_mul_cancel₀ ne) pos _ _
  have bound : avg masas L (fun x => if esExito x then 1 else 0) ≤ total masas L :=
    avg_mono masas L _ _ (fun x _ => by change (if esExito x.2 then (1:ℝ≥0) else 0)≤1; split <;> norm_num)
  rw [one] at bound
  exact NNReal.coe_le_coe.mpr bound

private theorem historia_positiva (hn : 0<count n q) : 0<(Fintype.card (Historia n q):ℝ) := by
  rw [card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]
  positivity

theorem transferencia_de_las_ramas (h : ℕ) (lev : q=n-h) (hn : 0<count n q) (u : ColorWeights ℝ≥0)
    (v : Historia n q → ℝ) (pos : ∀ H,0<v H)
    (pesos : ∀ H,(pesoCamino H h u).val=v H)
    (nz : ∀ (H : Historia n q) i,denominador (estado H h i.val) u (secuencia H i)≠0) :
    Real.exp (-costeRamas v) ≤ exitoE2 n h u ∧ KLcondicionado n q h u ≤ costeRamas v := by
  let s:=exitoE2 n h u
  let prob:=fun H : Historia n q => pesoCamino H h u
  have hit (H : Historia n q) := camino_completo H h lev u (nz H)
  have fib (P : Tablero n q) : ∑ d : Decoracion P,v ⟨P,d⟩ ≤ masaTablero P h u := by
    simpa only [←pesos] using suma_en_la_fibra P h lev u prob (fun _ => hit _)
  have mass : ∑ H,v H≤s := by
    unfold s exitoE2 terminalE2
    rw [←proyectar_arbol]
    simp_rw [←pesos]
    apply suma_de_atomos _ _ (fun H : Historia n q => (etiquetas H,estado H h (2*n-1))) _ hit
    · intro H; have ok := proyeccion_exitosa H h lev; exact if_pos ⟨ok.1,ok.2.1,ok.2.2.1⟩
    · exact fun _ _ eq => etiquetas_inyectivas (congrArg Prod.fst eq)
  have hc := historia_positiva hn
  haveI : Nonempty (Historia n q) := Fintype.card_pos_iff.mp (by exact_mod_cast hc)
  have s0 : 0<s := (Finset.sum_pos (fun H _ => pos H) Finset.univ_nonempty).trans_le mass
  have norm : ∑ _ : Historia n q,proba n q=1 := by
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hc.ne'
  have block := Entropia.condicionar_en_exito Finset.univ (fun _ => proba n q) v s
    (fun _ _ => inv_pos.mpr hc) (fun H _ => pos H) norm mass s0 (exito_maximo n h u)
  refine ⟨block.2.2.2,?_⟩
  apply le_trans _ block.2.2.1
  apply divergencia_del_tablero hn (fun H => v H/s) (fun P => masaTablero P h u/s)
    (fun H => div_pos (pos H) s0)
  · intro P
    have c : 0<Fintype.card (Decoracion P) := by rw [card_fibra,multiplicidad]; positivity
    haveI := Fintype.card_pos_iff.mp c
    exact div_pos ((Finset.sum_pos (fun d _ => pos ⟨P,d⟩) Finset.univ_nonempty).trans_le (fib P)) s0
  · intro P; rw [←Finset.sum_div]; exact div_le_div_of_nonneg_right (fib P) s0.le
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.transferencia_de_las_ramas
