import AdjuntoPonderadoDeLosDieciseisPatrones
import ParametrosDeLasRaicesDirectas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Repair
noncomputable section
open Classical

def coefDelPerfil {n} (h : ℕ) (p : FactoresContinuos) (y z : ℝ≥0) (u : Mark n) :=
  let θ:=fun (e : Cell n) => (↑(probDeLaCasilla h p e*y/z^4):ℝ)
  let η:=fun i => (↑(probLinea n h p (lineLabel (corners u).2 i)*y/z):ℝ)
  coefInverso (θ u.1) (θ u.2) (η 2) (η 3)

theorem cota_de_coeficientes_del_articulo {n h} {p : FactoresContinuos} {κ m ζ z y : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (zp : 0<ζ) (cut : ζ≤z) (y1 : y≤1)
    (u : Mark n) (t : CuatroMarcas) :
    let M:=m^4/κ^4
    let S:=max 1 (M/ζ^4)
    let D:=max 1 (M/ζ)
    |coefDelPerfil h p y z u t|≤(↑(S^2*D^2):ℝ)*(escalaDelPatron n t:ℝ) := by
  intro M S D
  let θ:=fun (e : Cell n) => probDeLaCasilla h p e*y/z^4
  let η:=fun i => probLinea n h p (lineLabel (corners u).2 i)*y/z
  have src (e) : θ e≤S*(n:ℝ≥0)⁻¹ := by
    have cap:=(cargas_acotadas (h:=h) hn sp kp (lineLabel e 0) e).2
    have bound : probArista n h p e*y/z^4≤M/ζ^4 :=
      div_le_div₀ (zero_le _) ((mul_le_mul' cap y1).trans_eq (mul_one M)) (pow_pos zp 4) (pow_le_pow_left' cut 4)
    have id : θ e=(probArista n h p e*y/z^4)*(n:ℝ≥0)⁻¹ := by
      dsimp only [θ,probDeLaCasilla]; simp only [div_eq_mul_inv]; ring
    rw [id]; exact mul_le_mul_right' (bound.trans (le_max_right _ _)) _
  have dst (i) : η i≤D := by
    have cap:=(cargas_acotadas (h:=h) hn sp kp (lineLabel (corners u).2 i) u.1).1
    exact (div_le_div₀ (zero_le _) ((mul_le_mul' cap y1).trans_eq (mul_one M)) zp cut).trans (le_max_right _ _)
  have src' (o : Bool) (e) : |if o then (1:ℝ) else ↑(θ e)|≤(↑(S*pesoDeUnaFuente n o):ℝ) := by
    cases o
    · simpa [pesoDeUnaFuente,abs_of_nonneg (θ e).property] using (NNReal.coe_le_coe.mpr (src e))
    · simp [pesoDeUnaFuente,S]
  have dst' (j : Bool) (i) : |if j then -(η i:ℝ) else 1|≤(D:ℝ) := by
    cases j
    · simp [D]
    · simpa [abs_of_nonneg (η i).property] using (NNReal.coe_le_coe.mpr (dst i))
  unfold coefDelPerfil coefInverso monoCuatro
  simp only [abs_mul]
  have step:=mul_le_mul (src' t.1 u.1) (src' t.2.1 u.2) (abs_nonneg _) (NNReal.coe_nonneg _)
  apply (mul_le_mul (mul_le_mul step (dst' t.2.2.1 2) (abs_nonneg _) (by positivity))
    (dst' t.2.2.2 3) (abs_nonneg _) (by positivity)).trans
  dsimp only [escalaDelPatron]; push_cast; exact le_of_eq (by ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_de_coeficientes_del_articulo
