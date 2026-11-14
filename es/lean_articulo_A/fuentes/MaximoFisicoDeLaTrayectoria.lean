import SeguimientoDeLosObservables
import Mathlib.Data.Finset.Lattice.Fold
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def errorDeCoordenada {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (z : ℝ≥0) (c : Activa n) : ℝ≥0 :=
  ⟨|(lectura p h X (coordenada c):ℝ)-blanco (n:=n) p h (coordenada c) z|,abs_nonneg _⟩

def errorDelEstado {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (z : ℝ≥0) :=
  Finset.univ.sup (errorDeCoordenada p h X z)

theorem error_alcanzado {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (z : ℝ≥0) :
    ∃ c : Activa n,errorDelEstado p h X z=errorDeCoordenada p h X z c := by
  have ne : (Finset.univ : Finset (Activa n)).Nonempty := ⟨.inl (.inl 0),Finset.mem_univ _⟩
  obtain ⟨c,_,eq⟩:=Finset.exists_mem_eq_sup _ ne (errorDeCoordenada p h X z)
  exact ⟨c,eq⟩

theorem dentro_del_maximo {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (z : ℝ≥0) (c : Activa n) :
    within masas (lectura p h X (coordenada c)) (blanco (n:=n) p h (coordenada c) z) (errorDelEstado p h X z) := by
  have small : errorDeCoordenada p h X z c≤errorDelEstado p h X z := Finset.le_sup (Finset.mem_univ _)
  have scalar (a b e : ℝ) (h : |a-b|≤e) : a≤b+e ∧ b≤a+e := by
    obtain ⟨lo,hi⟩:=abs_le.mp h; constructor <;> linarith
  exact scalar _ _ _ (NNReal.coe_le_coe.mpr small)

private theorem normalizar {Y V z E s : ℝ≥0} (H : within masas Y (V*z) E) :
    within masas (Y/s) ((V/s)*z) (E/s) := by
  have a:=scale masas s⁻¹ H
  change within masas (s⁻¹*Y) (s⁻¹*(V*z)) (s⁻¹*E) at a
  simpa only [←mul_assoc,inv_mul_eq_div] using a

theorem el_maximo_da_seguimiento {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (z : ℝ≥0)
    (reloj : (↑(X.reals+X.virtuals):ℝ≥0)=(↑(2*n-1):ℝ≥0)*z) :
    Seguimiento h p X z (errorDelEstado p h X z) := by
  have est:=dentro_del_maximo p h X z
  constructor
  · exact reloj
  · have H:=est (.inl (.inl 0))
    change within masas (lectura p h X .realCount) (blanco (n:=n) p h .realCount z) _ at H
    simp only [blanco,lectura_de_cuota,ordenFisico,pow_one] at H
    exact normalizar H
  · intro j live
    exact normalizar (est (.inr (j.1,⟨j.2,live.1⟩)))
  · have H:=est (.inl (.inl 1))
    change within masas (lectura p h X .boardWeight) (blanco (n:=n) p h .boardWeight z) _ at H
    simp only [blanco,lectura_del_tablero,ordenFisico] at H
    simpa only [div_div,←pow_two,totalIni] using (normalizar (s:=(n:ℝ≥0)) H)
  · intro i
    have H:=est (.inl (.inr i)); change within masas _ (blanco (n:=n) p h (.family i) z) _ at H
    simp only [blanco,ordenFisico,pow_one] at H
    exact normalizar H

theorem maximo_al_empezar (n h : ℕ) (p : FactoresContinuos) :
    errorDelEstado p h (initial n h) 1=0 := by
  obtain ⟨c,eq⟩:=error_alcanzado p h (initial n h) 1
  rw [eq]; apply NNReal.eq; simp [errorDeCoordenada,blanco]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.el_maximo_da_seguimiento
#print axioms ArticuloA.Historias.maximo_al_empezar
