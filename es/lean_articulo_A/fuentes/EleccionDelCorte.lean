import LogNormalizadoresPorRango
namespace ArticuloA.Rangos
open scoped BigOperators
noncomputable section
private theorem existe (D : ℕ) (d : 0<D) : ∃ K : ℕ,D^2≤K^3 := by
  refine ⟨D,?_⟩
  rw [pow_succ D 2]
  exact Nat.le_mul_of_pos_right _ d

def corte (D : ℕ) (d : 0<D) : ℕ := Nat.find (existe D d)

theorem corte_superior (D : ℕ) (d : 0<D) : D^2≤(corte D d)^3 := Nat.find_spec (existe D d)

theorem corte_inferior (D : ℕ) (d : 0<D) :
    0<corte D d ∧ corte D d≤D ∧ (corte D d-1)^3<D^2 := by
  have ok := corte_superior D d
  have pos : 0<corte D d := by
    by_contra! no
    rw [show corte D d=0 by omega] at ok
    simpa using (lt_of_lt_of_le (pow_pos d 2) ok)
  have le : corte D d ≤ D := Nat.find_min' (existe D d) (by
    rw [pow_succ D 2]; exact Nat.le_mul_of_pos_right _ d)
  have prev : corte D d-1<corte D d := by omega
  exact ⟨pos,le,lt_of_not_ge (Nat.find_min (existe D d) prev)⟩

theorem normalizadores_con_corte {D : ℕ} {c W : ℝ} (d : 0<D) (c0 : 0≤c) (wp : 0<W)
    (Y : ℕ→ℝ) (yp : ∀ m≤D,0<Y m)
    (env : ∀ m≤D,Y m/W≤((m:ℝ)/D)^4+c*((m:ℝ)/D)/(D+1)+c/(D+1)^2) :
    ∑ m ∈ Finset.range (D+1),Real.log (Y m) ≤ ((D:ℝ)+1)*Real.log W-4*((D:ℝ)+1)+4+
      (4+6*c)*(corte D d:ℝ) := suma_normalizadores (corte_inferior D d).1
        (corte_inferior D d).2.1 (corte_superior D d) c0 wp Y yp env
end
end ArticuloA.Rangos
#print axioms ArticuloA.Rangos.corte_inferior
#print axioms ArticuloA.Rangos.normalizadores_con_corte
