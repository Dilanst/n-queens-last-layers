import NormalizacionReal
import PositividadDesdeCruces
import Mathlib.Algebra.BigOperators.Field
open scoped BigOperators
namespace ArticuloA.Limites
open Repair
noncomputable section
open Classical

private def skipEmb {n} {a : Cell n} {xs : List (Cell n)} : Mask xs ↪ Mask (a::xs) :=
  ⟨Mask.skip,fun _ _ h => by cases h; rfl⟩
private def takeEmb {n} {a : Cell n} {xs : List (Cell n)} : Mask xs ↪ Mask (a::xs) :=
  ⟨Mask.take,fun _ _ h => by cases h; rfl⟩

def configuraciones {n} : (xs : List (Cell n)) → Finset (Mask xs)
  | [] => {Mask.empty}
  | _::xs => ((configuraciones xs).map skipEmb) ∪ ((configuraciones xs).map takeEmb)

private theorem ramas {n} (x : Cell n) (xs : List (Cell n)) :
    Disjoint ((configuraciones xs).map (skipEmb (a:=x))) ((configuraciones xs).map takeEmb) := by
  apply Finset.disjoint_left.mpr
  intro z hz ht
  obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hz
  obtain ⟨v,_,eq⟩ := Finset.mem_map.mp ht
  cases eq

theorem todas {n} {xs : List (Cell n)} (b : Mask xs) : b ∈ configuraciones xs := by
  induction b with
  | empty => simp [configuraciones]
  | skip b ih => exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_,ih,rfl⟩)
  | take b ih => exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨_,ih,rfl⟩)

private theorem sumaNat {n} (xs : List (Cell n)) (f : Mask xs → ℕ) :
    sumMasks xs f = ∑ p ∈ configuraciones xs, f p := by
  induction xs with
  | nil => simp [sumMasks,configuraciones]
  | cons x xs ih => rw [sumMasks,configuraciones,Finset.sum_union (ramas x xs),
      Finset.sum_map,Finset.sum_map,ih,ih]; rfl

private theorem sumaReal {n} (xs : List (Cell n)) (f : Mask xs → ℝ) :
    sumReal.masks xs f = ∑ p ∈ configuraciones xs, f p := by
  induction xs with
  | nil => simp [SumLaw.masks,configuraciones]
  | cons x xs ih =>
    change sumReal.masks xs (fun p => f (.skip p)) + sumReal.masks xs (fun p => f (.take p)) = _
    rw [configuraciones,Finset.sum_union (ramas x xs),Finset.sum_map,Finset.sum_map,ih,ih]; rfl

def nivel (n q : ℕ) : Finset (Placement n) := (configuraciones (board n)).filter (fun p => Legal p ∧ pieces p=q)

theorem cardinal_nivel (n q : ℕ) : (nivel n q).card = count n q := by
  unfold count nivel
  rw [sumaNat, Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  simp [layer]

def promedioNivel (n q : ℕ) (f : Placement n → ℝ) := (∑ p ∈ nivel n q, f p) / (count n q:ℝ)

private theorem promedio_fisico {n q : ℕ} (f : Placement n → ℝ)
    (lim : ∀ p, ¬(Legal p ∧ pieces p=q) → f p=0) :
    sumReal.masks (board n) f = ∑ p ∈ nivel n q, f p := by
  rw [sumaReal,nivel,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with h
  · rfl
  · exact lim p h

private theorem marcas_nulas {n : ℕ} (g : Mark n → ℝ) (hg : ∀ a,g a=0) : sumReal.marks g=0 := by
  have zero (l : List (Fin n)) : sumReal.over l (fun _ => (0:ℝ))=0 := by
    induction l with
    | nil => rfl
    | cons a l ih => change 0+sumReal.over l _=0; rw [ih,add_zero]
  rw [show g=(fun _ => 0) from funext hg]
  simp only [SumLaw.marks,zero]

theorem directa_uniforme (n h : ℕ) (w : Cell n → ℝ) :
    mediaD n h w = promedioNivel n (n-h) (fun p =>
      sumReal.marks (directWeight sumReal (n-h) w p)/((h:ℝ)^2*n)) := by
  unfold mediaD directo promedioNivel
  rw [promedio_fisico (q:=n-h),←Finset.sum_div]
  · ring
  · intro p hp
    apply marcas_nulas
    intro m
    have miss : ¬Direct (n-h) p m := fun d => hp ⟨d.2.1,d.1⟩
    simp [directWeight,miss,sumReal]

theorem inversa_uniforme (n h : ℕ) (w : Cell n → ℝ) :
    mediaI n h w = promedioNivel n (n-h+1) (fun p =>
      sumReal.marks (diagonalWeight sumReal (n-h) w p)/(n:ℝ)^2) := by
  unfold mediaI inverso promedioNivel
  rw [promedio_fisico (q:=n-h+1),←Finset.sum_div]
  · ring
  · intro p hp
    apply marcas_nulas
    intro m
    unfold diagonalWeight
    split_ifs with hx
    · exact (hp ⟨hx.2.1,hx.1⟩).elim
    · rfl
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.cardinal_nivel
#print axioms ArticuloA.Limites.directa_uniforme
#print axioms ArticuloA.Limites.inversa_uniforme
