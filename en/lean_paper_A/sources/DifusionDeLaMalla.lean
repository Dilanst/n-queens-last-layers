import OscilacionEspacialDelPeso
import ComparacionFinitaDelPerfil
open Set
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 RealFinita
noncomputable section

theorem medio_admisible {n i : ℕ} (hi : i<n) : medio n i∈unidadCerrada := by
  simpa [centro,nodo,medio] using centro_pertenece n i hi

theorem oblicuo_admisible (n : ℕ) (hn : 0<n) (j : Indice n) (a : ℝ) :
    oblicuo n a j.val∈Icc a (a+2) := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have bound : j.val+1≤2*n := by have t:=j.isLt; change j.val<2*n-1 at t; omega
  have rb : (j.val:ℝ)+1≤2*(n:ℝ) := by exact_mod_cast bound
  unfold oblicuo
  exact ⟨le_add_of_nonneg_right (by positivity),add_le_add_left ((div_le_iff₀ np).mpr rb) _⟩

theorem factores_positivos {n p κ M L} (hn : 0<n) (data : ControlEspacial p κ M L) (kp : 0<κ)
    (x : ℝ≥0) (xp : 0<x) : ∀ i j,0<factores (n:=n) (pesosMalla n x p) i j := by
  intro i j
  have d := oblicuo_admisible n hn j (-1); norm_num at d
  have a := oblicuo_admisible n hn j 0; norm_num at a
  fin_cases i <;> simp only [factores,pesosMalla]
  · split_ifs with hj
    · exact_mod_cast mul_pos (show 0<(x:ℝ) by exact_mod_cast xp) (kp.trans_le (data.R.minimo _ (medio_admisible hj)))
    · norm_num
  · split_ifs with hj
    · exact_mod_cast mul_pos (show 0<(x:ℝ) by exact_mod_cast xp) (kp.trans_le (data.C.minimo _ (medio_admisible hj)))
    · norm_num
  · exact kp.trans_le (data.D.minimo _ d)
  · exact kp.trans_le (data.A.minimo _ a)

def difusion_muestreada {n p κ M L} (hn : 2≤n) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (x y : ℝ≥0) (xp : 0<x) (y1 : (y:ℝ)≤1)
    (u : ColorWeights ℝ≥0)
    (ur : ∀ e : Cell n,wCelda u e=wCelda (sameColors (pesosMalla n x p)) e)
    (uv : ∀ i j,factores (n:=n) u.virtual i j=factores (pesosMalla n y p) i j) :
    Difusos n u (constanteDifusion (κ^4) (M^4) κ (M^4)) := by
  have np : 0<n := by omega
  have xr : 0<(x:ℝ) := by exact_mod_cast xp
  have bounds (e : Cell n) := limites_del_producto data kp.le _ _ (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
  have de (j : Indice n) : oblicuo n (-1) j.val∈Icc (-1) 1 := by convert oblicuo_admisible n np j (-1) using 1; norm_num
  have ae (j : Indice n) : oblicuo n 0 j.val∈Icc 0 2 := by simpa using oblicuo_admisible n np j 0
  have cap (i : Fin 4) (j : Indice n) : factores u.virtual i j≤M := by
    rw [uv]; fin_cases i <;> simp only [factores,pesosMalla]
    · split_ifs with hj
      · exact (mul_le_of_le_one_left (NNReal.coe_nonneg _) y1).trans (data.Rmax _ (medio_admisible hj))
      · exact m1
    · split_ifs with hj
      · exact (mul_le_of_le_one_left (NNReal.coe_nonneg _) y1).trans (data.Cmax _ (medio_admisible hj))
      · exact m1
    · exact data.Dmax _ (de j)
    · exact data.Amax _ (ae j)
  apply desde_cotas_de_factores hn u x (κ^4) (M^4) κ (M^4) xr (pow_pos kp _) (by positivity) kp (by positivity)
  · intro e; rw [ur,muestra_real,mul_comm (κ^4)]; exact mul_le_mul_of_nonneg_left (bounds e).1 (sq_nonneg _)
  · intro e; rw [ur,muestra_real,mul_comm (M^4)]; exact mul_le_mul_of_nonneg_left (bounds e).2 (sq_nonneg _)
  · intro z
    calc
      wTupla u z ≤ ∏ _i : Fin 4,M := by
        unfold wTupla pesoDe
        exact Finset.prod_le_prod (fun i _ => show 0≤factores u.virtual i (z i) from NNReal.coe_nonneg _) (fun i _ => cap i (z i))
      _ = M^4 := by simp
  · intro j hj; rw [uv]; simpa [factores,pesosMalla,not_lt.mpr hj] using k1
  · intro j hj; rw [uv]; simpa [factores,pesosMalla,not_lt.mpr hj] using k1
  · intro j; rw [uv]; exact data.D.minimo _ (de j)
  · intro j; rw [uv]; exact data.A.minimo _ (ae j)

def difusion_comun {n p κ M L} (hn : 2≤n) (data : ControlEspacial p κ M L) (kp : 0<κ)
    (k1 : κ≤1) (m1 : 1≤M) (x : ℝ≥0) (xp : 0<x) (x1 : (x:ℝ)≤1) :=
  difusion_muestreada hn data kp k1 m1 x x xp x1 (sameColors (pesosMalla n x p)) (fun _ => rfl) (fun _ _ => rfl)

def difusion_llena {n p κ M L} (hn : 2≤n) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) : Difusos n (coloresLlenos n (pesosMalla n 1 p))
      (constanteDifusion (κ^4) (M^4) κ (M^4)) := by
  apply difusion_muestreada hn data kp k1 m1 1 0 zero_lt_one (by norm_num)
  · intro e; unfold wCelda pesoDe; rw [Fin.prod_univ_four,Fin.prod_univ_four]; rfl
  · intro i j; fin_cases i <;> simp [factores,coloresLlenos,fullColors,pesosMalla,masas]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.difusion_comun
#print axioms ArticuloA.Historias.difusion_llena
#print axioms ArticuloA.Historias.factores_positivos
