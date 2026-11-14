import ColaInversaEnUnHorizonteDeE2
import EscalaExponencialDelConteoInverso
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Trayectoria.Adjunto

theorem cola_exponencial_del_conteo_inverso {n h T} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W)
    (ε s : ℝ) (ep : 0<ε) (st : 0<s)
    (sm : s*(2*(176*constanteRelojInverso κ m ζ W))≤1)
    (tilt : 32*(176*constanteRelojInverso κ m ζ W)^2*s≤ε)
    (size : cotaDerivaInversa κ m ζ C E W≤ε*n/4) :
    let S:=pasoDeRaiz (n:=n) h T p E
    let x:ℕ×State n:=(0,initial n h)
    let target:=blancoInverso h p w (horizonteInverso n T 0)
    (avg masas (rutas S 0 T x) (mark masas (fun l =>
      let last:=l.foldl (fun _ y => y) x
      last.1=T ∧ ε*(n:ℝ)^2≤|inversasDelTablero last.2.physical w-target|))).val ≤
      2*Real.exp (-(s*ε/4)*(n:ℝ)) := by
  intro S x target
  let B:=176*constanteRelojInverso κ m ζ W
  let U:=cotaDerivaInversa κ m ζ C E W
  have nr : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have time : T≤2*n := finT.trans (Nat.sub_le _ _)
  have time' : (T:ℝ)≤2*(n:ℝ) := by exact_mod_cast time
  have sc : (s/n)*(2*(B*n))=s*(2*B) := by field_simp; ring
  have theta:=div_nonneg st.le nr.le
  have bnd:=cola_inversa_en_un_horizonte hn hh sp kp m1 zp finT floor bal he ho w wp cap
    (s/n) (ε*n^2/2) theta (by rw [sc]; exact sm)
  have expbd:=exponente_del_conteo (show 0<n by omega) time st (B:=B) tilt
  apply le_trans _ (bnd.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr expbd) (by norm_num)))
  apply NNReal.coe_le_coe.mpr
  apply misma_masa_en_el_soporte
  intro i _ _ large
  obtain ⟨reached,bad⟩:=large
  refine ⟨reached,le_trans ?_ bad⟩
  have budget:=mul_le_mul_of_nonneg_left size (Nat.cast_nonneg (α:=ℝ) T)
  have horizon:=mul_le_mul_of_nonneg_right time' (div_nonneg (mul_nonneg ep.le nr.le) (by norm_num : (0:ℝ)≤4))
  nlinarith only [budget,horizon]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_exponencial_del_conteo_inverso
