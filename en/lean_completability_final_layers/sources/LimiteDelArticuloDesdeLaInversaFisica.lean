import DirectaDelArticuloConElPesoContinuo
import IntegralInversaDelPerfilLleno
open Set Filter
open scoped Topology
namespace ArticuloA.Historias
open Perfil Limites
noncomputable section

/-- The remaining random input is explicitly at level h-1, in probability,
with the spatial inverse weight used in both counts and the integral of Section 9. -/
theorem limite_con_la_unica_entrada_inversa {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b) (cont : ContinuidadEnElLleno p b)
    (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h)
    (inv : ∀ ε>0,Tendsto (fun n => desviacion n (n-h+1)
      (Iobs n h (fun z => 1/aDelLleno p b z))
      (integralTablero (fun r c => gammaDelPerfil (p 0) (b 0) r c/perfilDirectoContinuo (p 0) (b 0) r c)) ε)
      atTop (𝓝 0)) : Tendsto (fun n => fracReal n h) atTop (𝓝 (1/b 0)) := by
  let w:=fun (n : ℕ) (z : Cell n) => 1/aDelLleno p b z
  have hz : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bp := (rama.euler 0 hz).coef
  let m:=b 0*κ^8
  have mp : 0<m := mul_pos bp (pow_pos rama.kp _)
  have cap (n) (e : Cell n) : |w n e|≤1/m := by
    have lower : m≤aDelLleno p b e := piso_integral_del_cruce (rama.espacio 0 hz) rama.kp rama.lp bp
      (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
    change |1/aDelLleno p b e|≤_
    rw [abs_of_nonneg (div_nonneg zero_le_one (mp.le.trans lower))]
    exact div_le_div_of_nonneg_left zero_le_one mp lower
  have levels : ∀ᶠ n : ℕ in atTop,0<count n (n-h) ∧ 0<count n (n-h+1) := by
    filter_upwards [soluciones_eventuales_del_primer_orden first,eventually_ge_atTop h] with n sol nh
    refine ⟨capa_positiva_si_hay_solucion nh sol,?_⟩
    rw [show n-h+1=n-(h-1) by omega]
    exact capa_positiva_si_hay_solucion (by omega) sol
  rw [integral_del_cociente_del_articulo rama] at inv
  exact limite_por_eventos h hh w (b 0) (1/m) bp (by positivity) cap levels
    (directa_del_articulo rama pt cont first h hh).2.1 inv
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.limite_con_la_unica_entrada_inversa
