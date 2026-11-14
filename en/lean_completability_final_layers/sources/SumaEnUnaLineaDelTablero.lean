import MasasDeFuenteEnFilaYColumna
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

private theorem linea_en_una_fila {n} (i : Fin 4) (dif : i≠0) (r : Fin n) (j : ℕ) :
    (∑ c : Fin n,estadoEscalar (lines (r,c) i=j))≤1 := by
  apply suma_indicador_unico
  intro c d hc hd; apply Fin.ext
  have yes : i=1 ∨ i=2 ∨ i=3 := by omega
  rcases yes with rfl|rfl|rfl <;> simp [lines] at hc hd <;> omega

theorem masa_de_una_linea {n} (i : Fin 4) (j : ℕ) :
    (∑ e : Cell n,estadoEscalar (lines e i=j))≤n := by
  rw [Fintype.sum_prod_type]
  by_cases row : i=0
  · subst i; rw [Finset.sum_comm]
    apply (Finset.sum_le_sum (s:=Finset.univ) (fun c _ =>
      suma_indicador_unico (fun r : Fin n => lines (r,c) 0=j)
        (fun r s h g => Fin.ext (by simpa [lines] using h.trans g.symm)))).trans_eq
    simp
  · exact (Finset.sum_le_sum (s:=Finset.univ) (fun r _ => linea_en_una_fila i row r j)).trans_eq (by simp)

theorem masa_de_un_cruce_marcado {n} {X Y : State n} (lx : Legal X.physical) (ly : Legal Y.physical)
    (o v : Bool) (g : Cell n→ℝ) (pos : ∀ z,0≤g z) :
    (∑ u : Mark n,masaFuente X o u.1*masaFuente Y v u.2*g (corners u).2)≤∑ z,g z := by
  simp only [Fintype.sum_prod_type,corners]
  let a:=fun r j : Fin n => masaFuente X o (r,j)
  let b:=fun i c : Fin n => masaFuente Y v (i,c)
  change (∑ r,∑ j,∑ i,∑ c,a r j*b i c*g (i,j))≤∑ i,∑ j,g (i,j)
  have col (i j : Fin n) : ∑ r,∑ c,a r j*b i c*g (i,j)≤g (i,j) := by
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    have ha : (∑ r,a r j)≤1 := (masa_de_fila_columna lx o j).2
    have hb : (∑ c,b i c)≤1 := (masa_de_fila_columna ly v i).1
    have bound:=mul_le_mul ha hb (Finset.sum_nonneg (fun c _ => masaFuente_no_negativa Y v (i,c))) zero_le_one
    simpa only [one_mul] using mul_le_mul_of_nonneg_right bound (pos (i,j))
  have perm :
      (∑ r,∑ j,∑ i,∑ c,a r j*b i c*g (i,j))=∑ i,∑ j,∑ r,∑ c,a r j*b i c*g (i,j) := by
    conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl
    intro i _; rw [Finset.sum_comm]
  rw [perm]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => col i j))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_de_una_linea
#print axioms ArticuloA.Historias.masa_de_un_cruce_marcado
