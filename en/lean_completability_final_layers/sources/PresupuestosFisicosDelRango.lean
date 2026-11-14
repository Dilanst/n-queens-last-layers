import AtomoDeLaHistoria
import DelReveladoAlLog
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria.E2 Revelado
noncomputable section
open Classical
variable {n q : ℕ}

private theorem por_lista {α β : Type} [DecidableEq β] (S : Finset α) (g : α→β)
    (inj : Function.Injective g) (L : List β) (flag : β→Bool)
    (inside : ∀ a∈S,g a ∈ L ∧ flag (g a)=true) : S.card ≤ L.countP flag := by
  let E := (L.filter flag).toFinset
  have sub : S.image g ⊆ E := by
    intro b hb
    obtain ⟨a,hs,rfl⟩ := Finset.mem_image.mp hb
    exact List.mem_toFinset.mpr (List.mem_filter.mpr (inside a hs))
  rw [←Finset.card_image_of_injective S inj]
  exact (Finset.card_le_card sub).trans ((List.toFinset_card_le _).trans_eq (List.countP_eq_length_filter ..).symm)

private theorem necesaria (P : Tablero n q) (C : Completion P) (p : Indice n) (a : Candidata n)
    (bad : (otros P C p a).card≠4) :
    exceptional (aristasTotales P C) (edgeOf (pieza P C p)) (numeros a)=true := by
  cases h : exceptional (aristasTotales P C) (edgeOf (pieza P C p)) (numeros a) with
  | false => exact False.elim (bad (ordinaria P C p a h))
  | true => rfl

theorem reales_excepcionales (P : Tablero n q) (C : Completion P) (p : Indice n) :
    (Finset.univ.filter (fun e : Cell n => (otros P C p (tuplaReal e)).card≠4)).card ≤
      4*n+(2*n-1)*6 := by
  let flag:=fun e : Cell n => exceptional (aristasTotales P C) (edgeOf (pieza P C p)) (lines e)
  have a := por_lista (Finset.univ.filter (fun e : Cell n => (otros P C p (tuplaReal e)).card≠4))
    id Function.injective_id (board n) flag (fun e he =>
      ⟨board_complete e,necesaria P C p (tuplaReal e) (Finset.mem_filter.mp he).2⟩)
  exact a.trans (by simpa [flag,aristasTotales] using excepciones_reales n (aristasTotales P C) (edgeOf (pieza P C p)))

theorem virtuales_excepcionales (P : Tablero n q) (C : Completion P) (p : Indice n) :
    (Finset.univ.filter (fun a : Candidata n => (otros P C p a).card≠4)).card ≤ 10*(2*n-1)^3 := by
  let N:=2*n-1
  have inj : Function.Injective (@numeros n) := by
    intro a b eq; funext i; exact Fin.ext (congrFun eq i)
  have a := por_lista (Finset.univ.filter (fun a : Candidata n => (otros P C p a).card≠4))
    numeros inj (virtualEdges N) (exceptional (aristasTotales P C) (edgeOf (pieza P C p)))
    (fun a ha => ⟨en_cartesiana a,necesaria P C p a (Finset.mem_filter.mp ha).2⟩)
  have b := excepciones_virtuales N (aristasTotales P C) (edgeOf (pieza P C p))
  rw [show (aristasTotales P C).length=N by simp [aristasTotales,N]] at b
  exact a.trans (b.trans_eq (by change 4*(N*(N*N))+N*(6*(N*N))=10*N^3; ring))

theorem una_sola_marcada {β : Type} [Fintype β] (P : Tablero n q) (C : Completion P) (p : Indice n)
    (a : β→Candidata n) (inj : Function.Injective a) :
    (Finset.univ.filter (fun e : β => otros P C p (a e)=∅)).card≤1 := by
  apply Finset.card_le_one.mpr; intro e he f hf
  apply inj; funext i
  exact ((solo_la_marcada P C p (a e)).mp (Finset.mem_filter.mp he).2 i).trans
    (((solo_la_marcada P C p (a f)).mp (Finset.mem_filter.mp hf).2 i).symm)

theorem masa_de_excepciones {α : Type} [Fintype α] (w : α→ℝ) (bad : α→Prop) [DecidablePred bad] (M : ℝ)
    (cap : ∀ e,w e≤M) (M0 : 0≤M) (k : ℕ) (size : (Finset.univ.filter bad).card≤k) :
    (∑ e,if bad e then w e else 0)≤k*M := by
  rw [←Finset.sum_filter]
  calc
    _ ≤ ∑ _e ∈ Finset.univ.filter bad,M := Finset.sum_le_sum (fun _ _ => cap _)
    _ = _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr size) M0
private theorem escala {B Z M N W A : ℝ} {j : ℕ}
    (n1 : 1≤N) (m0 : 0≤M) (exc : B≤(10*N^j)*M) (mark : Z≤M)
    (diff : M*N^(j+1)≤A*W) (j1 : 1≤j) :
    B≤10*A*W/N ∧ Z≤A*W/N^2 := by
  have np : 0<N := by linarith
  constructor
  · apply (le_div_iff₀ np).mpr
    calc
      _ ≤ 10*N^j*M*N := mul_le_mul_of_nonneg_right exc np.le
      _ = 10*(M*N^(j+1)) := by rw [pow_succ]; ring
      _ ≤ 10*(A*W) := mul_le_mul_of_nonneg_left diff (by norm_num)
      _ = _ := by ring
  · apply (le_div_iff₀ (sq_pos_of_pos np)).mpr
    exact ((mul_le_mul_of_nonneg_right mark (sq_nonneg N)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ n1 (by omega : 2≤j+1)) m0)).trans diff

def masaEx {β : Type} [Fintype β] (w : β→ℝ) (f : β→Prop) [DecidablePred f] := ∑ e,if f e then w e else 0

theorem escala_fisica {β : Type} [Fintype β] (P : Tablero n q) (C : Completion P)
    (p : Indice n) (a : β→Candidata n) (inj : Function.Injective a) (N j : ℕ)
    (n1 : 1≤N) (j1 : 1≤j) (w : β→ℝ) (W M A : ℝ) (M0 : 0≤M) (cap : ∀ e,w e≤M)
    (diff : M*(N:ℝ)^(j+1)≤A*W)
    (bound : (Finset.univ.filter (fun e : β => (otros P C p (a e)).card≠4)).card≤10*N^j) :
    masaEx w (fun e => (otros P C p (a e)).card≠4)≤10*A*W/N ∧
    masaEx w (fun e => otros P C p (a e)=∅)≤A*W/(N:ℝ)^2 := by
  apply escala (j:=j) (by exact_mod_cast n1) M0 _ _ diff j1
  · have ex := masa_de_excepciones w (fun e => (otros P C p (a e)).card≠4) M cap M0 (10*N^j) bound
    simpa only [masaEx,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using ex
  · have sp := masa_de_excepciones w (fun e => otros P C p (a e)=∅) M cap M0 1 (una_sola_marcada P C p a inj)
    simpa only [masaEx,Nat.cast_one,one_mul] using sp
theorem presupuestos_reales (P : Tablero n q) (C : Completion P) (p : Indice n) (hn : 1≤n)
    (w : Cell n→ℝ) (W M A : ℝ) (M0 : 0≤M) (cap : ∀ e,w e≤M)
    (diff : M*(↑(2*n-1):ℝ)^2≤A*W) :
    masaEx w (fun e => (otros P C p (tuplaReal e)).card≠4)≤10*A*W/(2*n-1:ℕ) ∧
    masaEx w (fun e => otros P C p (tuplaReal e)=∅)≤A*W/(↑(2*n-1):ℝ)^2 := by
  have inj : Function.Injective (@tuplaReal n) := by
    intro e f h
    have row := congrArg Fin.val (congrFun h 0)
    have col := congrArg Fin.val (congrFun h 1)
    exact Prod.ext (Fin.ext row) (Fin.ext col)
  apply escala_fisica P C p tuplaReal inj (2*n-1) 1 (by omega) (by decide) w W M A M0 cap diff
  have b := reales_excepcionales P C p
  rw [pow_one]
  exact b.trans (by omega)

theorem presupuestos_virtuales (P : Tablero n q) (C : Completion P) (p : Indice n) (hn : 1≤n)
    (w : Candidata n→ℝ) (W M A : ℝ) (M0 : 0≤M) (cap : ∀ e,w e≤M)
    (diff : M*(↑(2*n-1):ℝ)^4≤A*W) :
    masaEx w (fun e => (otros P C p e).card≠4)≤10*A*W/(2*n-1:ℕ) ∧
    masaEx w (fun e => otros P C p e=∅)≤A*W/(↑(2*n-1):ℝ)^2 := by
  exact escala_fisica P C p id Function.injective_id (2*n-1) 3 (by omega) (by decide)
    w W M A M0 cap diff (virtuales_excepcionales P C p)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.presupuestos_reales
#print axioms ArticuloA.Historias.presupuestos_virtuales
#print axioms ArticuloA.Historias.escala_fisica
#print axioms ArticuloA.Historias.reales_excepcionales
#print axioms ArticuloA.Historias.virtuales_excepcionales
#print axioms ArticuloA.Historias.una_sola_marcada
