import MaximoFisicoDeLaTrayectoria
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def fraccionAntes (n t : ℕ) : ℝ≥0 := (↑((2*n-1)-t):ℝ≥0)/(↑(2*n-1):ℝ≥0)

theorem fraccion_al_empezar {n : ℕ} (hn : 2≤n) : fraccionAntes n 0=1 := by
  have nz : (↑(2*n-1):ℝ≥0)≠0 := by exact_mod_cast (by omega : 2*n-1≠0)
  simp only [fraccionAntes,Nat.sub_zero,div_self nz]

theorem fraccion_a_lo_sumo_uno {n : ℕ} (hn : 2≤n) (t : ℕ) : fraccionAntes n t≤1 := by
  have nz : 0<(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : 0<2*n-1)
  exact (div_le_one nz).mpr (by exact_mod_cast Nat.sub_le (2*n-1) t)

theorem fraccion_disminuye {n t : ℕ} (tN : t<2*n-1) :
    fraccionAntes n (t+1)+(↑(2*n-1):ℝ≥0)⁻¹=fraccionAntes n t := by
  have H : (2*n-1)-(t+1)+1=(2*n-1)-t := by omega
  unfold fraccionAntes; rw [←one_div,←add_div,←Nat.cast_one (R:=ℝ≥0),←Nat.cast_add,H]

theorem reloj_de_las_cuotas {n t : ℕ} {X : State n} (hn : 2≤n) (cuotas : X.reals+X.virtuals=(2*n-1)-t) :
    (↑(X.reals+X.virtuals):ℝ≥0)=(↑(2*n-1):ℝ≥0)*fraccionAntes n t := by
  have nz : (↑(2*n-1):ℝ≥0)≠0 := by exact_mod_cast (by omega : 2*n-1≠0)
  rw [cuotas]; unfold fraccionAntes
  have general (a b : ℝ≥0) (bp : b≠0) : a=b*(a/b) := by field_simp
  exact general _ _ nz

theorem fraccion_antes_del_horizonte {n t T : ℕ} {ζ : ℝ≥0} (tT : t≤T)
    (floor : ζ≤fraccionAntes n T) : ζ≤fraccionAntes n t := by
  apply floor.trans; apply div_le_div_of_nonneg_right _ (zero_le _)
  exact_mod_cast Nat.sub_le_sub_left tT (2*n-1)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.fraccion_disminuye
#print axioms ArticuloA.Historias.reloj_de_las_cuotas
