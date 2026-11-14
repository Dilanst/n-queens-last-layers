import CotasDeLasMediasFisicas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators
namespace ArticuloA.Limites
open Repair
noncomputable section
open Classical
variable {n : ℕ}
def cruces (p : Placement n) : Finset (Cell n) := Finset.univ.filter (emptyCross p)

private theorem tamano_libre (l : List (Fin n)) (nd : l.Nodup) :
    (Finset.univ \ l.toFinset).card=n-l.length := by
  rw [Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,List.toFinset_card_of_nodup nd]

theorem numero_cruces (p : Placement n) (hp : Legal p) :
    (cruces p).card = (n-pieces p)^2 := by
  let r := (queens p).map Prod.fst
  let c := (queens p).map Prod.snd
  have eq : cruces p = (Finset.univ \ r.toFinset) ×ˢ (Finset.univ \ c.toFinset) := by
    ext e
    simp only [cruces, Finset.mem_filter, Finset.mem_univ,true_and,Finset.mem_product,Finset.mem_sdiff,
      List.mem_toFinset,r,c,List.mem_map]
    constructor
    · intro h
      exact ⟨fun ⟨x,hx,eq⟩ => (h x hx).1 eq,fun ⟨x,hx,eq⟩ => (h x hx).2 eq⟩
    · rintro ⟨hr,hc⟩ x hx
      exact ⟨fun eq => hr ⟨x,hx,eq⟩,fun eq => hc ⟨x,hx,eq⟩⟩
  rw [eq,Finset.card_product,tamano_libre r (distinctRows hp),tamano_libre c (distinctColumns hp)]
  simp only [r,c,List.length_map,queenLength,pow_two]

theorem suma_lista_sin_repetidos {α : Type} [DecidableEq α] (l : List α) (nd : l.Nodup) (f : α → ℝ) :
    sumReal.over l f = ∑ x ∈ l.toFinset,f x := by
  induction l with
  | nil => simp [SumLaw.over,sumReal]
  | cons x l ih =>
    obtain ⟨no,hd⟩ := List.nodup_cons.mp nd
    rw [List.toFinset_cons,Finset.sum_insert (by simpa using no)]
    exact congrArg (f x + ·) (ih hd)

private theorem indices (f : Fin n → ℝ) : sumReal.over (List.finRange n) f = ∑ i,f i := by
  rw [suma_lista_sin_repetidos _ (List.nodup_finRange _)]; simp

theorem suma_real_de_marcas (f : Mark n → ℝ) :
    sumReal.marks f = ∑ z : Cell n, ∑ y : Cell n, f (z,y) := by
  simp only [SumLaw.marks,indices,Fintype.sum_prod_type]

private theorem por_cruce (w : Cell n → ℝ) (p : Placement n) (q : ℕ) (z : Cell n) :
    ∑ y : Cell n,directWeight sumReal q w p (z,y) = w z * (crossDegree q p z:ℝ) := by
  have list (xs : List (Cell n)) : sumReal.over xs (fun y => directWeight sumReal q w p (z,y)) =
      w z * (counting.over xs (fun y => directWeight counting q (fun _ => 1) p (z,y)):ℝ) := by
    induction xs with
    | nil => simp [SumLaw.over,sumReal,counting]
    | cons e xs ih =>
      change directWeight sumReal q w p (z,e) + sumReal.over xs _ =
        w z * ((directWeight counting q (fun _ => 1) p (z,e) + counting.over xs _:ℕ):ℝ)
      rw [Nat.cast_add,mul_add,ih]; by_cases h : Direct q p (z,e) <;> simp [directWeight,sumReal,counting,h]
  have all : (board n).toFinset = Finset.univ := by ext e; simp [board_complete]
  rw [←all,←suma_lista_sin_repetidos _ (board_unique n)]
  exact list _

theorem suma_directa_fisica (p : Placement n) (q : ℕ) (w : Cell n → ℝ) :
    sumReal.marks (directWeight sumReal q w p) = ∑ z ∈ cruces p, w z * (crossDegree q p z:ℝ) := by
  rw [suma_real_de_marcas]
  unfold cruces
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro z _
  by_cases yes : emptyCross p z
  · rw [if_pos yes,por_cruce]
  · rw [if_neg yes]
    exact Finset.sum_eq_zero (fun y _ => by
      have no : ¬Direct q p (z,y) := fun d => yes d.2.2.1
      simp [directWeight,no,sumReal])

def mediaCruces (p : Placement n) (h : ℕ) (t : Cell n → ℝ) :=
  (∑ z ∈ cruces p,t z)/(h:ℝ)^2

theorem error_reponderado (p : Placement n) (h : ℕ) (hh : 0<h) (nh : h≤n)
    (hp : Legal p) (size : pieces p=n-h) (a t : Cell n → ℝ) (m T η : ℝ)
    (mpos : 0<m) (apos : ∀ z,m≤a z) (ct : ∀ z, |t z|≤T)
    (error : ∀ z ∈ cruces p, |(crossDegree (n-h) p z:ℝ)/n-a z|≤η) :
    |Dobs n h (fun z => t z/a z) p-mediaCruces p h t| ≤ (T/m)*η := by
  have cap := numero_cruces p hp
  rw [size,show n-(n-h)=h by omega] at cap
  have hn : (n:ℝ)≠0 := by exact_mod_cast (lt_of_lt_of_le hh nh).ne'
  have H : (0:ℝ)<h := by exact_mod_cast hh
  let f := fun z => (t z/a z)*((crossDegree (n-h) p z:ℝ)/n-a z)
  have eq : Dobs n h (fun z => t z/a z) p-mediaCruces p h t=(∑ z∈cruces p,f z)/(h:ℝ)^2 := by
    unfold Dobs mediaCruces
    rw [suma_directa_fisica,←div_div,div_right_comm,←sub_div,Finset.sum_div,←Finset.sum_sub_distrib]
    apply congrArg (· / (h:ℝ)^2)
    apply Finset.sum_congr rfl; intro z _
    dsimp [f]; field_simp [hn,(lt_of_lt_of_le mpos (apos z)).ne']; ring
  have bound : ∀ z∈cruces p, |f z| ≤ (T/m)*η := by
    intro z hz
    rw [abs_mul,abs_div,abs_of_pos (lt_of_lt_of_le mpos (apos z))]
    exact mul_le_mul (div_le_div_of_nonneg_left (abs_nonneg _) mpos (apos z) |>.trans
      (div_le_div_of_nonneg_right (ct z) mpos.le)) (error z hz) (abs_nonneg _) (div_nonneg ((abs_nonneg _).trans (ct z)) mpos.le)
  rw [eq,abs_div,abs_of_pos (sq_pos_of_pos H)]
  apply (div_le_iff₀ (sq_pos_of_pos H)).mpr
  calc
    _ ≤ ∑ z∈cruces p, |f z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z∈cruces p, (T/m)*η := Finset.sum_le_sum bound
    _ = _ := by simp [cap,mul_comm]
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.numero_cruces
#print axioms ArticuloA.Limites.error_reponderado
