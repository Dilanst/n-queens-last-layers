import NormalizadorDeLaPiezaMarcada
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel
noncomputable section
open Classical

structure FactoresContinuos where
  fila : ℝ→ℝ≥0
  columna : ℝ→ℝ≥0
  diagonal : ℝ→ℝ≥0
  anti : ℝ→ℝ≥0

def medio (n i : ℕ) : ℝ := ((i:ℝ)+1/2)/n
def oblicuo (n : ℕ) (a : ℝ) (i : ℕ) := a+((i:ℝ)+1)/n
def pesosMalla (n : ℕ) (x : ℝ≥0) (p : FactoresContinuos) : Fin 4→ℕ→ℝ≥0
  | 0 => fun i => if i<n then x*p.fila (medio n i) else 1
  | 1 => fun i => if i<n then x*p.columna (medio n i) else 1
  | 2 => fun i => p.diagonal (oblicuo n (-1) i)
  | 3 => fun i => p.anti (oblicuo n 0 i)

def pesoContinuo (p : FactoresContinuos) (r c : ℝ) : ℝ :=
  (p.fila r:ℝ)*p.columna c*p.diagonal (r-c)*p.anti (r+c)

theorem nodos_de_una_casilla {n : ℕ} (e : Cell n) :
    oblicuo n (-1) (lines e 2)=medio n e.1.val-medio n e.2.val ∧
    oblicuo n 0 (lines e 3)=medio n e.1.val+medio n e.2.val := by
  have c:=e.2.isLt
  have np : (n:ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  have eq : (lines e 2)+e.2.val+1=e.1.val+n := by dsimp [lines]; omega
  have re : (lines e 2:ℝ)+(e.2.val:ℝ)+1=(e.1.val:ℝ)+n := by exact_mod_cast eq
  constructor
  · unfold oblicuo medio
    rw [show (lines e 2:ℝ)=(e.1.val:ℝ)+n-e.2.val-1 by linarith]
    field_simp; ring
  · simp only [oblicuo,medio,lines,Nat.cast_add,zero_add]; ring

theorem muestra_real {n : ℕ} (x : ℝ≥0) (p : FactoresContinuos) (e : Cell n) :
    wCelda (sameColors (pesosMalla n x p)) e=(x:ℝ)^2*pesoContinuo p (medio n e.1.val) (medio n e.2.val) := by
  obtain ⟨d,a⟩ := nodos_de_una_casilla e
  unfold wCelda pesoDe
  rw [Fin.prod_univ_four]
  change ((pesosMalla n x p 0 e.1.val:ℝ)*pesosMalla n x p 1 e.2.val)*
    pesosMalla n x p 2 (lines e 2)*pesosMalla n x p 3 (lines e 3)=_
  simp only [pesosMalla,e.1.isLt,e.2.isLt,if_true,NNReal.coe_mul,d,a,pesoContinuo]
  ring

theorem Wreal_malla (n : ℕ) (x : ℝ≥0) (p : FactoresContinuos) :
    Wreal n (sameColors (pesosMalla n x p))=
      (x:ℝ)^2*(∑ i∈Finset.range n,∑ j∈Finset.range n,pesoContinuo p (medio n i) (medio n j)) := by
  unfold Wreal
  simp_rw [muestra_real]
  rw [←Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_range]
  
theorem Wreal_lleno_malla (n : ℕ) (p : FactoresContinuos) :
    Wreal n (coloresLlenos n (pesosMalla n 1 p))=Wreal n (sameColors (pesosMalla n 1 p)) := by
  apply Finset.sum_congr rfl; intro e _
  unfold wCelda pesoDe
  rw [Fin.prod_univ_four,Fin.prod_univ_four]
  rfl

theorem cuatro_sumas_virtuales (n : ℕ) (u : ColorWeights ℝ≥0) :
    Wvirtual n u=∏ i : Fin 4,∑ j : Indice n,factores u.virtual i j := by
  unfold Wvirtual wTupla pesoDe
  exact (Fintype.prod_sum _).symm

theorem suma_de_fisicas_y_ficticias (n : ℕ) (hn : 1≤n) (v : ℕ→ℝ) (d : ℝ) :
    (∑ i : Indice n, if i.val<n then v i.val else d)=∑ i∈Finset.range n,v i+(↑(n-1):ℝ)*d := by
  change (∑ i : Fin (2*n-1),(fun j : ℕ => if j<n then v j else d) i.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j<n then v j else d) (2*n-1)]
  rw [show 2*n-1=n+(n-1) by omega,Finset.sum_range_add]
  have a : (∑ i∈Finset.range n,if i<n then v i else d)=∑ i∈Finset.range n,v i :=
    Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))
  simp [a,nsmul_eq_mul]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.nodos_de_una_casilla
#print axioms ArticuloA.Historias.Wreal_malla
#print axioms ArticuloA.Historias.cuatro_sumas_virtuales
