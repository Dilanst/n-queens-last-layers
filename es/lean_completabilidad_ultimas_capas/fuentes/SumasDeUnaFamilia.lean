import IndicesFisicosDelPerfil
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel RealFinita
noncomputable section
open Classical
def familiaReal (n : ℕ) (v : ℝ→ℝ) := ∑ i∈Finset.range n,v (medio n i)
def familiaOblicua (n : ℕ) (a : ℝ) (v : ℝ→ℝ) := ∑ i∈Finset.range (2*n-1),v (oblicuo n a i)

private theorem suma_de_log_fisicos (n : ℕ) (hn : 1≤n) (x : ℝ≥0) (xp : 0<x) (v : ℝ→ℝ≥0)
    (pos : ∀ i<n,0<v (medio n i)) :
    (∑ i : Indice n,Real.log ((if i.val<n then x*v (medio n i.val) else 1 : ℝ≥0):ℝ))=
      (n:ℝ)*Real.log x + familiaReal n (fun y => Real.log (v y)) := by
  have eq (i : Indice n) : Real.log ((if i.val<n then x*v (medio n i.val) else 1 : ℝ≥0):ℝ)=
      if i.val<n then Real.log x+Real.log (v (medio n i.val)) else 0 := by
    split_ifs with hi
    · rw [NNReal.coe_mul,Real.log_mul (by exact_mod_cast xp.ne') (by exact_mod_cast (pos i.val hi).ne')]
    · simp
  simp_rw [eq,suma_de_fisicas_y_ficticias n hn (fun i => Real.log x+Real.log (v (medio n i))) 0]
  simp [Finset.sum_add_distrib,nsmul_eq_mul,familiaReal]

theorem suma_de_log_malla (n : ℕ) (hn : 1≤n) (x : ℝ≥0) (xp : 0<x) (p : FactoresContinuos)
    (hr : ∀ i<n,0<p.fila (medio n i)) (hc : ∀ i<n,0<p.columna (medio n i)) :
    (∑ f,∑ j : Indice n,Real.log (factores (pesosMalla n x p) f j))=
      2*n*Real.log x+familiaReal n (fun y => Real.log (p.fila y))+familiaReal n (fun y => Real.log (p.columna y))+
      familiaOblicua n (-1) (fun y => Real.log (p.diagonal y))+familiaOblicua n 0 (fun y => Real.log (p.anti y)) := by
  rw [Fin.sum_univ_four]
  let u:=pesosMalla n x p
  have row := suma_de_log_fisicos n hn x xp p.fila hr
  have col := suma_de_log_fisicos n hn x xp p.columna hc
  change (∑ j : Indice n,Real.log (factores u 0 j))+(∑ j : Indice n,Real.log (factores u 1 j))+
      (∑ j : Indice n,Real.log (factores u 2 j))+(∑ j : Indice n,Real.log (factores u 3 j))=_
  change (∑ j : Indice n,Real.log (factores u 0 j))=_ at row
  change (∑ j : Indice n,Real.log (factores u 1 j))=_ at col
  rw [row,col]; unfold familiaOblicua
  simp_rw [Finset.sum_range]
  simp only [factores,u,pesosMalla]; ring

theorem efectivos_de_la_malla (n : ℕ) (x : ℝ≥0) (p : FactoresContinuos) :
    efectivos (factores (n:=n) (pesosMalla n x p))=factores (n:=n) (pesosMalla n x p) := by
  funext f j
  fin_cases f <;> by_cases small : j.val<n <;> simp [efectivos,factores,pesosMalla,small,show n≤j.val ↔ ¬j.val<n by omega]

theorem masa_transversal (n : ℕ) (hn : 1≤n) (x : ℝ≥0) (v : ℝ→ℝ≥0) :
    (∑ j : Indice n,((if j.val<n then x*v (medio n j.val) else 1 : ℝ≥0):ℝ))=
      (x:ℝ)*familiaReal n (fun y => (v y:ℝ))+(↑(n-1):ℝ) := by
  have eq (j : Indice n) : ((if j.val<n then x*v (medio n j.val) else 1 : ℝ≥0):ℝ)=
      if j.val<n then (x:ℝ)*v (medio n j.val) else 1 := by split_ifs <;> simp
  simp_rw [eq,suma_de_fisicas_y_ficticias n hn (fun i => (x:ℝ)*v (medio n i)) 1]
  rw [←Finset.mul_sum,mul_one]; rfl

def sumasVirtuales (n : ℕ) (u : ColorWeights ℝ≥0) (i : Fin 4) := ∑ j : Indice n,factores u.virtual i j

theorem sumas_comunes (n : ℕ) (hn : 1≤n) (x : ℝ≥0) (p : FactoresContinuos) :
    let U:=sumasVirtuales n (sameColors (pesosMalla n x p))
    U 0=(x:ℝ)*familiaReal n (fun y => p.fila y)+(↑(n-1):ℝ) ∧
    U 1=(x:ℝ)*familiaReal n (fun y => p.columna y)+(↑(n-1):ℝ) ∧
    U 2=familiaOblicua n (-1) (fun y => p.diagonal y) ∧ U 3=familiaOblicua n 0 (fun y => p.anti y) := by
  refine ⟨masa_transversal n hn x _,masa_transversal n hn x _,?_,?_⟩ <;>
    unfold familiaOblicua <;> rw [Finset.sum_range] <;> rfl

theorem sumas_llenas (n : ℕ) (hn : 1≤n) (p : FactoresContinuos) :
    let U:=sumasVirtuales n (coloresLlenos n (pesosMalla n 1 p))
    U 0=(↑(n-1):ℝ) ∧ U 1=(↑(n-1):ℝ) ∧ U 2=familiaOblicua n (-1) (fun y => p.diagonal y) ∧
    U 3=familiaOblicua n 0 (fun y => p.anti y) := by
  have val (i : Indice n) : ((if i.val<n then 0 else 1 : ℝ≥0):ℝ)=if i.val<n then 0 else 1 := by split_ifs <;> simp
  have R : (∑ i : Indice n,((if i.val<n then 0 else 1 : ℝ≥0):ℝ))=(↑(n-1):ℝ) := by
    simp_rw [val,suma_de_fisicas_y_ficticias n hn (fun _ => 0) 1]; simp
  refine ⟨R,R,?_,?_⟩ <;> unfold familiaOblicua <;> rw [Finset.sum_range] <;> rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_de_log_malla
#print axioms ArticuloA.Historias.sumas_comunes
#print axioms ArticuloA.Historias.sumas_llenas
