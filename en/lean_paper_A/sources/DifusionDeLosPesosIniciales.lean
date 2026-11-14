import SumaFisicaDeNormalizadores
open scoped BigOperators
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
variable {n : ℕ}

/-- A uniform lower bound after removing the common factor x² from the real weights. -/
theorem difusion_real_inicial (w : Cell n→ℝ) (x b B : ℝ) (xb : 0<b) (B0 : 0≤B)
    (low : ∀ e,b*x^2≤w e) :
    (B*x^2)*(↑(2*n-1):ℝ)^2 ≤ (4*B/b)*(∑ e,w e) := by
  have hN : (↑(2*n-1):ℝ)≤2*n := by exact_mod_cast (Nat.sub_le (2*n) 1)
  have square := pow_le_pow_left₀ (Nat.cast_nonneg (2*n-1):0≤(↑(2*n-1):ℝ)) hN 2
  have lb : (n:ℝ)^2*(b*x^2)≤∑ e,w e := by
    have u := Finset.sum_le_sum (s:=Finset.univ) (fun e _ => low e)
    simpa [Fintype.card_prod,pow_two,nsmul_eq_mul] using u
  have c0 : 0≤4*B/b := by positivity
  calc
    _ ≤ (B*x^2)*(2*(n:ℝ))^2 := mul_le_mul_of_nonneg_left square (by positivity)
    _ = (4*B/b)*((n:ℝ)^2*(b*x^2)) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lb c0

def ficticias (n : ℕ) : Finset (Indice n) := Finset.univ.filter (fun j => n ≤ j.val)

theorem numero_ficticias (hn : 1≤n) : (ficticias n).card=n-1 := by
  let E : Fin (n-1) ↪ Indice n :=
    ⟨fun i => ⟨n+i.val,by have := i.isLt; omega⟩,fun i j h => Fin.ext (by have v:=congrArg Fin.val h; dsimp at v; omega)⟩
  have eq : ficticias n=Finset.univ.map E := by
    ext i; constructor
    · intro hi; have low := (Finset.mem_filter.mp hi).2
      apply Finset.mem_map.mpr
      refine ⟨⟨i.val-n,by have := i.isLt; omega⟩,Finset.mem_univ _,Fin.ext (by dsimp [E]; omega)⟩
    · rintro hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_add_right _ _⟩
  rw [eq,Finset.card_map,Finset.card_univ,Fintype.card_fin]

/-- The two row/column coordinates may have zero weights away from the fictitious indices. -/
theorem masa_de_familia (v : Indice n→ℝ) (b : ℝ) (hn : 1≤n) (nn : ∀ i,0≤v i)
    (fict : ∀ i : Indice n,n ≤ i.val → b≤v i) : (↑(n-1):ℝ)*b≤∑ i,v i := by
  have a := Finset.sum_le_sum (s:=ficticias n) (fun i hi => fict i (Finset.mem_filter.mp hi).2)
  rw [Finset.sum_const,numero_ficticias hn,nsmul_eq_mul] at a
  exact a.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => nn i))

theorem masa_de_familia_completa (v : Indice n→ℝ) (b : ℝ) (low : ∀ i,b≤v i) :
    (↑(2*n-1):ℝ)*b≤∑ i,v i := by
  simpa [nsmul_eq_mul] using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => low i)

theorem difusion_virtual_inicial (hn : 2≤n) (v : Fin 4→Indice n→ℝ) (b B : ℝ)
    (b0 : 0<b) (B0 : 0≤B) (nn : ∀ i j,0≤v i j)
    (row : ∀ j : Indice n,n ≤ j.val → b≤v 0 j) (col : ∀ j : Indice n,n ≤ j.val → b≤v 1 j)
    (diag : ∀ j,b≤v 2 j) (anti : ∀ j,b≤v 3 j) :
    B*(↑(2*n-1):ℝ)^4 ≤ (9*B/b^4)*(∑ a : Candidata n,pesoDe v a) := by
  let N : ℝ := (2*n-1:ℕ)
  let H : ℝ := (n-1:ℕ)
  have n0 : 0≤N := by dsimp [N]; positivity
  have h0 : 0≤H := by dsimp [H]; positivity
  have tri : N≤3*H := by dsimp [N,H]; exact_mod_cast (by omega : 2*n-1≤3*(n-1))
  have r := masa_de_familia (v 0) b (by omega) (nn 0) row
  have c := masa_de_familia (v 1) b (by omega) (nn 1) col
  have d := masa_de_familia_completa (v 2) b diag
  have a := masa_de_familia_completa (v 3) b anti
  have npos : ∀ i,0≤∑ t,v i t := fun i => Finset.sum_nonneg (fun j _ => nn i j)
  have low : H*b*(H*b)*(N*b)*(N*b)≤∑ t : Candidata n,pesoDe v t := by
    change _ ≤ ∑ t : Candidata n,∏ i,v i (t i)
    rw [←Fintype.prod_sum,Fin.prod_univ_four]
    exact mul_le_mul (mul_le_mul (mul_le_mul r c (by positivity) (npos 0)) d (by positivity)
      (mul_nonneg (npos 0) (npos 1))) a (by positivity) (mul_nonneg (mul_nonneg (npos 0) (npos 1)) (npos 2))
  have first := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ n0 tri 2) (sq_nonneg N)
  calc
    _ ≤ B*((3*H)^2*N^2) := by
      change B*N^4≤_
      exact mul_le_mul_of_nonneg_left (by nlinarith only [first]) B0
    _ = (9*B/b^4)*(H*b*(H*b)*(N*b)*(N*b)) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.difusion_real_inicial
#print axioms ArticuloA.Historias.difusion_virtual_inicial
