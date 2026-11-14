import ParametrosDeLasRaicesDirectas
import GeometriaDeLaInversa
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

theorem fuentes_excluidas_por_cruce {n} (z : Cell n) :
    (board n).countP (fun e => decide (¬filterG z e))≤4*n := by
  apply Nat.le_trans _ (by simpa using excepciones_reales n [] (lines z))
  apply List.countP_mono_left; intro e _ bad
  have geom : filterG z e ↔ compatible z e := by
    simp only [filterG,compatible,corners]
    tauto
  have no : ¬compatible z e := fun h => (decide_eq_true_eq.mp bad) (geom.mpr h)
  rw [separadas] at no
  obtain ⟨j,eq⟩:=Classical.not_forall.mp no
  simp only [exceptional,List.any_nil,Bool.or_false]
  exact List.any_eq_true.mpr ⟨j,by simp [List.finRange,List.mem_ofFn]; omega,
    beq_iff_eq.mpr (Classical.not_not.mp eq).symm⟩

theorem masa_exacta_de_fuentes {n h} (p : FactoresContinuos) (np : 0<n) {κ m : ℝ≥0} {L : ℝ}
    (sp : ControlEspacial p κ m L) (kp : 0<κ) :
    masas.sum (board n) (probDeLaCasilla h p)=(↑(n-h):ℝ≥0) := by
  have n0 : (n:ℝ≥0)≠0 := by exact_mod_cast np.ne'
  have w0 : totalIni n h p≠0 := (lt_of_lt_of_le (pow_pos kp 4) (suelo_total_fisico np sp)).ne'
  let a:ℝ≥0:=cuotaR n h/totalIni n h p/n
  have same (e : Cell n) : probDeLaCasilla h p e=vInicial p e*a := by
    dsimp [probDeLaCasilla,probArista,a]; simp only [div_eq_mul_inv]; ring
  rw [funext same,show masas.sum (board n) (fun e => vInicial p e*a)=masas.sum (board n) (vInicial p)*a from Cart.sum_scale masas _ _ a]
  have initialSum : masas.sum (board n) (vInicial p)=masaN p (initial n h) := by
    unfold masaN boardSum; simp [E2.available,initial,List.all_eq_true]
  rw [initialSum]
  have scaled : masaN p (initial n h)=totalIni n h p*(n:ℝ≥0)^2 :=
    (div_mul_cancel₀ _ (pow_ne_zero 2 n0)).symm
  rw [scaled]; unfold a cuotaR; field_simp; ring

theorem masa_descartada_por_cruce {n} (z : Cell n) (π : Cell n→ℝ≥0) (M : ℝ≥0)
    (cap : ∀ e,(n:ℝ≥0)*π e≤M) :
    masas.sum (board n) (fun e => if filterG z e then 0 else π e) ≤ 4*M := by
  have np : 0<(n:ℝ≥0) := by exact_mod_cast (Nat.zero_lt_of_lt z.1.isLt)
  have bound (l : List (Cell n)) :
      masas.sum l (fun e => if filterG z e then 0 else π e)≤
        (↑(l.countP (fun e => decide (¬filterG z e))):ℝ≥0)*(M/n) := by
    induction l with
    | nil => simp [MassScale.sum,masas]
    | cons e l ih =>
      change (if filterG z e then 0 else π e)+_≤_
      rw [List.countP_cons]
      by_cases g : filterG z e
      · simpa [g] using ih
      · have ec : π e≤M/n := (le_div_iff₀ np).mpr (by simpa only [mul_comm] using cap e)
        simpa [g,Nat.cast_add,add_mul,add_comm] using add_le_add ec ih
  apply (bound _).trans
  calc _ ≤ (4*(n:ℝ≥0))*(M/n) := mul_le_mul_right' (by exact_mod_cast fuentes_excluidas_por_cruce z) _
       _ = _ := by field_simp; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_exacta_de_fuentes
#print axioms ArticuloA.Historias.masa_descartada_por_cruce
