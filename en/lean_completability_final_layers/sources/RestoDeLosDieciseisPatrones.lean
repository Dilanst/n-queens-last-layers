import BalanceDelPasoInverso
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.ProfileKernel Corte RealFinita Repair
noncomputable section
abbrev CuatroMarcas := Bool × Bool × Bool × Bool

private theorem sobre_el_soporte {α} (l : List α) (g : α→ℝ) (v : α→ℝ≥0) (B : ℝ)
    (bound : ∀ u∈l,|g u|≤B) :
    |(l.map (fun u => g u*(v u:ℝ))).sum|≤B*(masas.sum l v:ℝ) := by
  induction l with
  | nil => simp [MassScale.sum,masas]
  | cons u l ih =>
    change |g u*(v u:ℝ)+(l.map _).sum|≤B*((v u:ℝ)+(masas.sum l v:ℝ))
    rw [mul_add]
    apply (abs_add_le _ _).trans; rw [abs_mul,abs_of_nonneg (NNReal.coe_nonneg (v u))]
    exact add_le_add (mul_le_mul_of_nonneg_right (bound u List.mem_cons_self) (v u).property)
      (ih (fun x hx => bound x (List.mem_cons_of_mem _ hx)))

def soporteInverso {n} (X : State n) (t : CuatroMarcas) :=
  soporteDeParejas X t.1 t.2.1 t.2.2.1 t.2.2.2
def escalaDelPatron (n : ℕ) (t : CuatroMarcas) :=
  pesoDeUnaFuente n t.1*pesoDeUnaFuente n t.2.1

theorem exceso_con_pesos_con_signo {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (leg : Legal X.physical) (W : ℝ) (wp : 0≤W) (coef : CuatroMarcas→Mark n→ℝ)
    (cap : ∀ t,∀ u∈soporteInverso X t,|coef t u|≤W*(escalaDelPatron n t:ℝ)) :
    let row:=choices masas X (coloresDelPerfil n h p) (·⁻¹)
    let excess:=fun (t : CuatroMarcas) (u : Mark n) => meanN masas row (fun a =>
      deathsOn (diez u.1 u.2) (golpeDelPar u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2 a)-1)
    |∑ t : CuatroMarcas,((soporteInverso X t).map (fun u => coef t u*(excess t u:ℝ))).sum| ≤
      16*W*((45*(m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)):ℝ≥0):ℝ) := by
  intro row excess
  let H:=45*(m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4))
  have one (t : CuatroMarcas) :
      |((soporteInverso X t).map (fun u => coef t u*(excess t u:ℝ))).sum|≤W*(H:ℝ) := by
    have raw:=resto_del_paso_ponderado hn hh sp kp m1 zp hz z1 bal he ho X reg leg
      t.1 t.2.1 t.2.2.1 t.2.2.2
    have rel : (escalaDelPatron n t:ℝ)*(masas.sum (soporteInverso X t) (excess t):ℝ)≤(H:ℝ) :=
      NNReal.coe_le_coe.mpr raw
    apply (sobre_el_soporte _ _ _ _ (cap t)).trans
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left rel wp
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun t _ => one t)).trans
  have cnt : Fintype.card CuatroMarcas=16 := by decide
  simp only [Finset.sum_const,Finset.card_univ,cnt,nsmul_eq_mul,Nat.cast_ofNat]
  dsimp only [H]; ring_nf; rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.exceso_con_pesos_con_signo
