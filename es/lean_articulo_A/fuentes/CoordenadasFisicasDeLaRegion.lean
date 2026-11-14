import GradoDelEstadoInicial
import FibrasDeRegularidad
import EscalaRegionalReal
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Limites
noncomputable section

def masaN {n} (p : FactoresContinuos) (X : State n) := boardSum (n:=n) masas (vInicial p) (fun e => E2.available X (lines e))
def gradoN {n} (p : FactoresContinuos) (X : State n) (j : Vertex) := auxDegree masas X (vInicial p) j
def familiaN {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (i : Fin 4) :=
  Cart.part masas X (coloresDelPerfil n h p).virtual i
def factorRealN (n h : ℕ) : ℝ≥0 := if h=0 then 1 else (fraccionHuecos n h)^2

theorem factor_real_positivo {n h : ℕ} (hn : 0<n) : 0<factorRealN n h := by
  unfold factorRealN; split_ifs with hz
  · exact zero_lt_one
  · exact pow_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hz) (by exact_mod_cast hn)) 2

theorem factor_real_del_color {n h} (p : FactoresContinuos) (e : Cell n) :
    weights masas (coloresDelPerfil n h p).real (lines e)=factorRealN n h*vInicial p e := by
  apply NNReal.eq
  calc
    _ = wCelda (coloresDelPerfil n h p) e := cuatro_pesos _ (tuplaReal e)
    _ = _ := by rw [pesos_reales_para_el_estado]; change escalaReal n h*pesoFisico n p e=(factorRealN n h:ℝ)*pesoFisico n p e
                unfold escalaReal factorRealN; split_ifs <;> rfl

theorem suma_de_pesos_local {α : Type} [DecidableEq α] (l : List α) (nd : l.Nodup) (v : α→ℝ≥0) :
    (masas.sum l v).val=∑ e∈l.toFinset,(v e:ℝ) := by
  rw [←suma_lista_sin_repetidos l nd]
  induction l with
  | nil => rfl
  | cons e l ih =>
    change (v e:ℝ)+(masas.sum l v:ℝ)=(v e:ℝ)+Limites.sumReal.over l _
    exact congrArg ((v e:ℝ)+·) (ih (List.nodup_cons.mp nd).2)

theorem masa_del_estado {n} (p : FactoresContinuos) (X : State n) : (masaN p X:ℝ)=masaActiva p X := by
  unfold masaN boardSum masaActiva
  apply Eq.trans (suma_de_pesos_local _ (board_unique n) _)
  have all : (board n).toFinset=Finset.univ := by ext e; simp [board_complete]
  rw [all]; apply Finset.sum_congr rfl
  intro e _; cases he : E2.available X (lines e) <;> simp [he,peso_para_el_nucleo,masas]

theorem masa_cuando_empieza (n h : ℕ) (p : FactoresContinuos) : (masaN p (initial n h):ℝ)=Wfisico n p := by
  rw [masa_del_estado]; unfold masaActiva Wfisico
  simp [E2.available,initial,List.all_eq_true]

theorem suma_virtual_del_estado {n} (p : FactoresContinuos) (h : ℕ) (X : State n) (i : Fin 4) :
    (familiaN p h X i:ℝ)=virtualActiva h p X i := by
  unfold familiaN Cart.part
  rw [←List.map_coe_finRange,Cart.sum_map]
  apply Eq.trans (suma_de_pesos_local _ (List.nodup_finRange _) (fun j : Indice n =>
    if X.active i j.val then (coloresDelPerfil n h p).virtual i j.val else 0))
  simp only [List.toFinset_finRange]
  apply Finset.sum_congr rfl; intro j _
  cases bit : X.active i j.val <;> simp [bit,holguraInicial,factores]

theorem suma_virtual_inicial (n h : ℕ) (p : FactoresContinuos) (i : Fin 4) :
    (familiaN p h (initial n h) i:ℝ)=virtualInicial (n:=n) h p i := by
  rw [suma_virtual_del_estado]; simp [virtualActiva,initial,virtualInicial]

theorem grado_controlado_por_la_fibra {n} (p : FactoresContinuos) (X : State n) (j : Vertex) (m : ℝ≥0)
    (cap : ∀ e : Cell n,vInicial p e≤m) : gradoN p X j ≤ (n:ℝ≥0)*m := by
  let live:=fun e : Cell n => hitsVertex (lines e) j && otherLive X j.1 (lines e)
  have cnt : (board n).countP live≤n :=
    (List.countP_mono_left (fun e _ he => (Bool.and_eq_true_iff.mp he).1)).trans (fiber_cap j.1 j.2)
  have h:=Adjunto.on_bits masas (board n) live (vInicial p) m (fun e _ _ => cap e)
  exact le_trans h (show masas.times ((board n).countP live) m≤(n:ℝ≥0)*m by
    rw [times_m,ns_real]; exact mul_le_mul_right' (by exact_mod_cast cnt) m)

theorem peso_tupla_controlado {n} (u : ColorWeights ℝ≥0) (m : ℝ≥0)
    (cap : ∀ i j,j<2*n-1 → u.virtual i j≤m) (g : Edge) (mem : g∈virtualEdges (2*n-1)) :
    weights masas u.virtual g≤m^4 := by
  simp only [virtualEdges,List.mem_flatMap,List.mem_map,List.mem_range] at mem
  obtain ⟨i,hi,j,hj,d,hd,a,ha,rfl⟩:=mem
  change (_*_)*(_*_)≤m^4
  calc
    _ ≤ (m*m)*(m*m) := mul_le_mul' (mul_le_mul' (cap 0 i hi) (cap 1 j hj)) (mul_le_mul' (cap 2 d hd) (cap 3 a ha))
    _ = _ := by ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.grado_controlado_por_la_fibra
#print axioms ArticuloA.Historias.peso_tupla_controlado
