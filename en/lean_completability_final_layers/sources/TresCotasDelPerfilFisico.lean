import DifusionDeLaMalla
import CondicionesDelPerfilKL
import KLDelRevelado
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2 RealFinita
noncomputable section

def presupuesto (n h : ℕ) (hn : 2≤n) (κ M L m₀ s₁ Eb : ℝ) :=
  n*Real.log n+n*s₁-Real.log (count n n)+restoRango n hn (amplitudPerfil κ M)+
    errorPerfil κ M L m₀+Eb+h*Real.log 2+2*Real.log h.factorial

def Tres (n h : ℕ) (u : ColorWeights ℝ≥0) (d : ℝ) : Prop :=
  KLtrazas n (n-h) h u≤d ∧ Real.exp (-d)≤exitoE2 n h u ∧ KLcondicionado n (n-h) h u≤d

theorem Tres.aumentar {n h u a d} (ha : Tres n h u a) (bd : a≤d) : Tres n h u d :=
  ⟨ha.1.trans bd,(Real.exp_le_exp.mpr (neg_le_neg bd)).trans ha.2.1,ha.2.2.trans bd⟩

theorem comparacion_del_perfil_con_huecos {n h p κ M L b m₀} (src : PerfilKL n h p κ M L b m₀)
    (hn : 2≤n) (hal : 2*h≤n) (sol : 0<count n n) (x : ℝ≥0) (xp : 0<x)
    (x1 : (x:ℝ)≤1) (cuota : (x:ℝ)*(n:ℝ)=(h:ℝ)) (s s₁ Eb : ℝ)
    (euler : (n:ℝ)*s=(↑(n-h):ℝ)*(-Real.log (b/(x:ℝ)^2)-3)-(n:ℝ)*entropiaDeFactores p x)
    (borde : (n:ℝ)*(s-s₁)≤2*h*Real.log n+Eb) :
    Tres n h (sameColors (pesosMalla n x p)) (presupuesto n h hn κ M L m₀ s₁ Eb) := by
  let u:=sameColors (pesosMalla n x p)
  let A:=amplitudPerfil κ M
  have np : 0<n := by omega
  have hd : Difusos n u A := difusion_comun hn src.espacial src.kpos src.k1 src.m1 x xp x1
  have t := tres_cotas_comunes hn h (q:=n-h) rfl (capa_positiva_si_hay_solucion (by omega : h≤n) sol)
    _ (factores_positivos np src.espacial src.kpos x xp) A hd
  apply Tres.aumentar (a:=cotaKL n (n-h) hn u A (factores (pesosMalla n x p))) t
  have v:= log_Wvirtual_desde_sumas n h hn (by omega) u _ hd.vpos (masas_virtuales src hn x x1 cuota)
  have z:=coste_frente_al_tablero_lleno n h hn hal sol u _ A _ _ s s₁ _ _ _ Eb
    (masa_log_real src np (by omega) x xp hd.rpos) v (producto_log src np x xp) euler borde
  unfold presupuesto errorPerfil
  dsimp only [u,A] at z ⊢
  linarith only [z]

set_option maxHeartbeats 260000 in
theorem comparacion_del_perfil_lleno {n p κ M L b m₀} (src : PerfilKL n 0 p κ M L b m₀)
    (hn : 2≤n) (sol : 0<count n n) (s₁ : ℝ)
    (euler : s₁=(-Real.log b-3)-entropiaDeFactores p 1) :
    Tres n 0 (coloresLlenos n (pesosMalla n 1 p)) (presupuesto n 0 hn κ M L m₀ s₁ 0) := by
  let u:=coloresLlenos n (pesosMalla n 1 p)
  let A:=amplitudPerfil κ M
  have np : 0<n := by omega
  have hd : Difusos n u A := difusion_llena hn src.espacial src.kpos src.k1 src.m1
  have t : Tres n 0 u (cotaKL n n hn u A (factores (pesosMalla n 1 p))) := by
    unfold Tres
    simpa only [efectivos_de_la_malla,Nat.sub_zero] using
      tres_cotas_en_lleno hn sol (pesosMalla n 1 p) (factores_positivos np src.espacial src.kpos 1 zero_lt_one) A hd
  apply t.aumentar
  have pos : 0<Wreal n (sameColors (pesosMalla n 1 p)) := by rw [←Wreal_lleno_malla]; exact hd.rpos
  have real := masa_log_real src np (by simpa using np) 1 zero_lt_one pos
  simp only [Nat.sub_zero,NNReal.coe_one,one_pow,div_one] at real
  rw [←Wreal_lleno_malla] at real
  have vs := masas_virtuales src hn 0 (by norm_num) (by simp)
  have fullV (j : Fin 4) : sumasVirtuales n u j-((n:ℝ)+(0:ℕ)-1)≤2*L+2 := by
    calc
      _ = sumasVirtuales n (sameColors (pesosMalla n 0 p)) j-((n:ℝ)+(0:ℕ)-1) :=
        congrArg (fun a : ℝ => a-((n:ℝ)+(0:ℕ)-1)) (virtual_lleno_equivale_a_x_cero n hn p j)
      _ ≤ _ := vs j
  have virtual := log_Wvirtual_desde_sumas n 0 hn (Nat.zero_le _) u (2*L+2) hd.vpos fullV
  have e : (n:ℝ)*s₁=(↑(n-0):ℝ)*(-Real.log b-3)-(n:ℝ)*entropiaDeFactores p 1 := by rw [euler,Nat.sub_zero]; ring
  have z := coste_frente_al_tablero_lleno n 0 hn (by omega) sol u (factores (pesosMalla n 1 p)) A
    (-Real.log b) (entropiaDeFactores p 1) s₁ s₁ (2*(4*M^3*L)/m₀) (4*(2*L+2)) (6*(L/κ)) 0 real virtual
    (producto_log src np 1 zero_lt_one) e (by simp)
  unfold presupuesto errorPerfil
  dsimp only [u,A,Nat.sub_zero] at z ⊢
  linarith only [z]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.comparacion_del_perfil_con_huecos
#print axioms ArticuloA.Historias.comparacion_del_perfil_lleno
