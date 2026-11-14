import CuadraturaDeUnaDiagonalFisica
import DifusionDeLaMalla
open Set MeasureTheory
open scoped Interval BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

def gradoInicial (n : ℕ) (p : FactoresContinuos) (i : Fin 4) (j : Indice n) :=
  ∑ e : Cell n,if lines e i=j.val then pesoFisico n p e else 0

theorem grado_fibra {n} (p : FactoresContinuos) (a : Bool) (j : Indice n) :
    gradoInicial n p (verticeOblicuo a) j=gradoOblicuo n p a j := by
  unfold gradoInicial gradoOblicuo
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (fun e => by simp) _

def trazaTransversal (p : FactoresContinuos) (n j : ℕ) (col : Bool) (t : ℝ) :=
  if col then pesoContinuo p t (medio n j) else pesoContinuo p (medio n j) t
def integralTransversal (p : FactoresContinuos) (n j : ℕ) (col : Bool) :=
  ∫ t in (0:ℝ)..1,trazaTransversal p n j col t

theorem suma_transversal {n} (p : FactoresContinuos) (col : Bool) (j : Indice n) (hj : j.val<n) :
    gradoInicial n p (if col then 1 else 0) j=
      ∑ i : Fin n,trazaTransversal p n j.val col (medio n i.val) := by
  let r : Fin n := ⟨j.val,hj⟩
  have eq (i : Fin n) : i.val=j.val ↔ i=r := ⟨fun t => Fin.ext t,fun t => congrArg Fin.val t⟩
  cases col
  · unfold gradoInicial
    rw [Fintype.sum_prod_type]
    simp only [Bool.false_eq_true,ite_false,lines,trazaTransversal,pesoFisico,eq]
    rw [Finset.sum_comm]; simp [r]
  · unfold gradoInicial
    rw [Fintype.sum_prod_type]
    simp only [ite_true,lines,trazaTransversal,pesoFisico,eq]
    simp [r]

theorem grado_transversal_ficticio {n} (p : FactoresContinuos) (col : Bool) (j : Indice n) (hj : n≤j.val) :
    gradoInicial n p (if col then 1 else 0) j=0 := by
  apply Finset.sum_eq_zero; intro e _
  have r := e.1.isLt; have c := e.2.isLt
  cases col <;> simp [lines,show e.1.val≠j.val by omega,show e.2.val≠j.val by omega]

theorem cuadratura_transversal_fisica {n p κ M L} (hn : 0<n) (data : ControlEspacial p κ M L)
    (m0 : 0≤M) (l0 : 0≤L) (col : Bool) (j : Indice n) (hj : j.val<n) :
    |gradoInicial n p (if col then 1 else 0) j-(n:ℝ)*integralTransversal p n j.val col|≤4*M^3*L := by
  let L₀:=4*M^3*L
  let f:=trazaTransversal p n j.val col
  have lp : 0≤L₀ := by dsimp [L₀]; positivity
  have lip : ∀ s∈unidadCerrada,∀ t∈unidadCerrada,|f s-f t|≤L₀*|s-t| := by
    intro s hs t ht
    have jm := medio_admisible hj
    cases col
    · simpa only [f,trazaTransversal,Bool.false_eq_true,ite_false,sub_self,abs_zero,zero_add,L₀] using
        variacion_del_peso data l0 _ _ _ _ jm jm hs ht
    · simpa only [f,trazaTransversal,ite_true,sub_self,abs_zero,add_zero,L₀] using
        variacion_del_peso data l0 _ _ _ _ hs ht jm jm
  have e:=cuadratura_centros n hn f L₀ lp (continua_de_cota lp lip) lip
  rw [suma_transversal p col j hj,abs_sub_comm]
  rw [Finset.sum_range] at e
  simpa only [f,integralTransversal,centro,nodo,medio,zero_add,L₀] using e

def integralLinea (p : FactoresContinuos) (n j : ℕ) : Fin 4→ℝ
  | 0 => if j<n then integralTransversal p n j false else 0
  | 1 => if j<n then integralTransversal p n j true else 0
  | 2 => integralOblicua p n j false
  | 3 => integralOblicua p n j true

theorem cuadratura_grado_inicial {n p κ M L} (hn : 0<n) (data : ControlEspacial p κ M L)
    (m0 : 0≤M) (l0 : 0≤L) (i : Fin 4) (j : Indice n) :
    |gradoInicial n p i j-(n:ℝ)*integralLinea p n j.val i|≤2*(4*M^3*L) := by
  have pos : 0≤4*M^3*L := by positivity
  have line (col : Bool) :
      |gradoInicial n p (if col then 1 else 0) j-(n:ℝ)*(if j.val<n then integralTransversal p n j.val col else 0)|≤
        2*(4*M^3*L) := by
    by_cases t : j.val<n
    · rw [if_pos t]; exact (cuadratura_transversal_fisica hn data m0 l0 col j t).trans (by linarith)
    · rw [if_neg t,grado_transversal_ficticio p col j (Nat.le_of_not_gt t)]; simp; linarith
  have ob (a : Bool) := cuadratura_del_grado_oblicuo hn data m0 l0 a j
  fin_cases i
  · exact line false
  · exact line true
  · simpa only [←grado_fibra] using ob false
  · simpa only [←grado_fibra] using ob true
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cuadratura_grado_inicial
