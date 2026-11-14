import PrefijoDeE2
namespace ArticuloA.Historias
open Trayectoria.E2
noncomputable section
open Classical
variable {n q : ℕ}
private theorem total_colores (xs : List Bool) : xs.count true+xs.count false=xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [List.count_cons] at * <;> omega

theorem cuotas_del_estado (H : Historia n q) (h : ℕ) (level : q=n-h)
    (t : ℕ) (lim : t≤2*n-1) :
    let resto := (palabra H).drop t
    (estado H h t).reals = resto.count true ∧ (estado H h t).virtuals=resto.count false ∧
      (estado H h t).failed=false := by
  have len : (palabra H).length=2*n-1 := by simp [palabra,lista]
  induction t with
  | zero =>
    have all := total_colores (palabra H)
    rw [reales_contadas,len] at all
    simp only [estado,initial,List.drop_zero]
    exact ⟨level.symm.trans (reales_contadas H).symm,by omega,trivial⟩
  | succ t ih =>
    have ht : t<2*n-1 := by omega
    obtain ⟨R,V,F⟩ := ih (by omega)
    have idx : t < (palabra H).length := len ▸ ht
    have hd : (palabra H)[t] = esReal (secuencia H ⟨t,ht⟩) := by simp [palabra,lista]
    rw [List.drop_eq_getElem_cons idx,hd] at R V
    rw [estado,dif_pos ht]
    cases eq : secuencia H ⟨t,ht⟩ with
    | real e =>
      simp [eq,esReal,List.count_cons] at R V
      simp only [jugada,next,F,and_true]; omega
    | virtual a =>
      simp [eq,esReal,List.count_cons] at R V
      simp only [jugada,next,F,and_true]; omega

theorem fin_de_cuotas (H : Historia n q) (h : ℕ) (level : q=n-h) :
    (estado H h (2*n-1)).reals=0 ∧ (estado H h (2*n-1)).virtuals=0 ∧
      (estado H h (2*n-1)).failed=false := by
  have len : (palabra H).length=2*n-1 := by simp [palabra,lista]
  have hc := cuotas_del_estado H h level (2*n-1) le_rfl
  simpa only [List.drop_eq_nil_of_le len.le,List.count_nil] using hc
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuotas_del_estado
#print axioms ArticuloA.Historias.fin_de_cuotas
