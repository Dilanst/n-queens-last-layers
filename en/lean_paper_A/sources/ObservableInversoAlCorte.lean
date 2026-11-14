import CrucesDeLaConfiguracion
import CorteInversoConSigno
open scoped BigOperators
namespace ArticuloA.Limites
open Repair Trayectoria.E2
noncomputable section
open Classical
private theorem marca_elegible {n} (p : Placement n) (m : Mark n) :
    m ∈ invMarks p ↔ m.1≠m.2 ∧ m.1∈queens p ∧ m.2∈queens p ∧ freeDiagonals p (corners m).2 := by
  rcases m with ⟨e,f⟩
  simp [invMarks,grid,List.mem_flatMap,eligiblePair]
  tauto

theorem marcas_inversas_del_nivel {n q} (p : Placement n) (legal : Legal p) (size : pieces p=q+1)
    (w : Cell n → ℝ) :
    sumReal.marks (diagonalWeight sumReal q w p) = totalInverso sumaCampo w p := by
  have nd : (queens p).Nodup := legal.imp (fun h eq => h.1 (congrArg Prod.fst eq))
  have gridnd : (grid (queens p) (queens p)).Nodup := nd.product nd
  have marksnd : (invMarks p).Nodup := gridnd.filter _
  change _ = sumReal.over (invMarks p) _
  rw [suma_real_de_marcas,←Fintype.sum_prod_type,suma_lista_sin_repetidos _ marksnd]
  have S : (invMarks p).toFinset = Finset.univ.filter (fun m : Mark n => m∈invMarks p) := by ext m; simp
  rw [S,Finset.sum_filter]
  apply Finset.sum_congr rfl; intro m _
  simp only [marca_elegible,diagonalWeight,legal,size,true_and,sumReal]

/-- The cutoff bound acts on the observable appearing in the physical double count.
The configuration at the cut may have a different number of pieces. -/
theorem inversa_fisica_al_corte {n h t} {p u : Placement n} (hn : 0<n)
    (path : TerminalPath p t u) (legal : Legal u) (size : pieces u=n-h+1)
    (w : Cell n → ℝ) (M : ℝ) (hM : 0≤M) (cap : ∀ z,|w z|≤M) :
    |Iobs n h w u-totalInverso sumaCampo w p/(n:ℝ)^2| ≤ 4*((t:ℝ)/n)*M := by
  have N : 0<(n:ℝ) := by exact_mod_cast hn
  unfold Iobs
  rw [marcas_inversas_del_nivel u legal size,←sub_div,abs_div,abs_of_pos (sq_pos_of_pos N),abs_sub_comm]
  have H := div_le_div_of_nonneg_right (corte_con_signo path w M hM cap) (sq_nonneg (n:ℝ))
  calc
    _ ≤ _ := H
    _ = _ := by field_simp; ring
end
end ArticuloA.Limites
#print axioms ArticuloA.Limites.marcas_inversas_del_nivel
#print axioms ArticuloA.Limites.inversa_fisica_al_corte
