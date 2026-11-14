import SaltoDelCompensador
import PesosYCuotasAntesDelCorte
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Repair Corte
noncomputable section
open Classical

def valorDeRaiz {n} (N m d : ℕ) (z : Cell n) (p : Cell n→Fin 4→ℝ≥0) (π : Cell n→ℝ≥0) (X : State n) : ℝ :=
  (rootPart masas (·⁻¹) N m d z p π X false).val - (rootPart masas (·⁻¹) N m d z p π X true).val

def blancoDeLaRaiz {n} (y : ℝ≥0) (z : Cell n) (p : Cell n→Fin 4→ℝ≥0) (π : Cell n→ℝ≥0) :=
  masas.sum (board n) (fun e => (if filterG z e then y*π e else 0)*masas.four (fun i => 1-y*p e i))

theorem inicio_de_la_raiz {n} (h N T : ℕ) (np : 0<N) (cut : T≤N) (z : Cell n)
    (p : Cell n→Fin 4→ℝ≥0) (π : Cell n→ℝ≥0) (hp : ∀ e i,p e i≤1) :
    valorDeRaiz N N T z p π (initial n h) = (blancoDeLaRaiz ((T:ℝ≥0)/N) z p π:ℝ) := by
  let y:ℝ≥0:=(T:ℝ≥0)/N
  have nz : (N:ℝ≥0)≠0 := by exact_mod_cast np.ne'
  have yr : ratio masas (·⁻¹) T N=y := by
    unfold ratio; rw [ns_real,ns_real]; exact inv_mul_eq_div ..
  have feed0 (e : Cell n) := initial_feed masas (·⁻¹) (fun _ h => inv_mul_cancel₀ h) N T (π e)
    (by rw [ns_real]; exact nz)
  have hy : y≤1 := (div_le_one (by exact_mod_cast np)).mpr (by exact_mod_cast cut)
  let d := fun e i => (1:ℝ≥0)-y*p e i
  have one (e : Cell n) (i : Fin 4) : masas.add (d e i) (masas.mul y (p e i))=1 := by
    exact tsub_add_cancel_of_le ((mul_le_mul' hy (hp e i)).trans_eq (one_mul 1))
  let F := fun e j => signedPart masas (initial n h) z e (p e) y (y*π e) j
  have parts (e : Cell n) := initial_value masas n h z e (p e) (d e) y (y*π e) (one e)
  have eq (l : List (Cell n)) : masas.sum l (fun e => F e false)=
      masas.sum l (fun e => (if filterG z e then y*π e else 0)*masas.four (d e))+
      masas.sum l (fun e => F e true) := by
    exact (congrArg (masas.sum l) (funext parts)).trans (add_sum masas l _ _)
  unfold valorDeRaiz rootPart
  simp only [feed0,yr]
  have sum:=congrArg NNReal.toReal (eq (board n))
  change (masas.sum (board n) (fun e => F e false):ℝ)-(masas.sum (board n) (fun e => F e true):ℝ)=_
  rw [NNReal.coe_add] at sum
  change (masas.sum (board n) (fun e => F e false):ℝ) - _ = (masas.sum (board n) (fun e => (if filterG z e then y*π e else 0)*masas.four (d e)):ℝ)
  linarith only [sum]

theorem fin_de_la_raiz_en_el_corte {n} (N m : ℕ) (z : Cell n) (p : Cell n→Fin 4→ℝ≥0)
    (π : Cell n→ℝ≥0) (X : State n) :
    valorDeRaiz N m 0 z p π X = (physicalCount X.physical z:ℝ) := by
  have zeroRatio : ratio masas (·⁻¹) 0 m=0 := by unfold ratio; rw [ns_real]; change _*(0:ℝ≥0)=_; exact mul_zero _
  have zeroFeed (u : ℝ≥0) : feed masas (·⁻¹) u 0 m=0 := by
    unfold feed; rw [ns_real]; exact (show (↑(0:ℕ):ℝ≥0)*_=0 by simp)
  unfold valorDeRaiz rootPart
  simp only [zeroRatio,zeroFeed]
  have term (e : Cell n) (j : Bool) : signedPart masas X z e (p e) (0:ℝ≥0) 0 j= _ := terminal_value masas X z e (p e) j
  simp_rw [term]
  have count (l : List (Cell n)) : masas.sum l (fun e => if false=false ∧ Candidate X.physical z e then masas.one else masas.zero)=
      (counting.over l (fun e => indicator (Candidate X.physical z e)):ℝ≥0) := by
    induction l with
    | nil => change (0:ℝ≥0)=(↑(0:ℕ):ℝ≥0); simp
    | cons e l ih =>
      change _+masas.sum l _=(↑(indicator (Candidate X.physical z e)+counting.over l _):ℝ≥0)
      rw [Nat.cast_add,ih]; congr 1
      by_cases h : Candidate X.physical z e <;> simp [h,indicator,masas]
  have nilSum (l : List (Cell n)) : masas.sum l (fun e => if true=false ∧ Candidate X.physical z e then masas.one else masas.zero)=0 := by
    induction l with
    | nil => rfl
    | cons e l ih => change (if true=false ∧ Candidate X.physical z e then (1:ℝ≥0) else 0)+masas.sum l _=0; rw [ih]; simp
  simp only [eq_self,true_and] at count ⊢
  rw [count,nilSum]; change (↑(physicalCount X.physical z):ℝ)-0=_; exact sub_zero _

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.inicio_de_la_raiz
#print axioms ArticuloA.Historias.fin_de_la_raiz_en_el_corte
