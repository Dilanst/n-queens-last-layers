import SumaTemporalDelLogaritmoDeUnaHolgura
import HolguraTemporalDelPesoDeGTrasFijarLaReserva
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem suma_de_las_cargas_por_incidencia {n} (p : Cell n→ℝ) (g : FibraDeB1 n→ℝ) :
    (∑ e,p e*∑ i : Fin 4,g (etiquetaDeCasilla e i))=
      ∑ j : FibraDeB1 n,masaBajo p (enLaFibra j)*g j := by
  classical
  unfold masaBajo
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have one (j : FibraDeB1 n) :
      pesoCuando (enLaFibra j e) (p e)*g j=
       ∑ i : Fin 4,if etiquetaDeCasilla e i=j then p e*g j else 0:=by
    let i:=familiaDeReserva j
    have ee : enLaFibra j e ↔ etiquetaDeCasilla e i=j:=by
      rcases j with ⟨c,s⟩|⟨c,s⟩ <;> cases c <;> simp [i,familiaDeReserva,enLaFibra,etiquetaDeCasilla,etiquetaD,etiquetaA]
    rw [Finset.sum_eq_single i]
    · by_cases yes : enLaFibra j e
      · simp [pesoCuando,yes,ee.mp yes]
      · simp [pesoCuando,yes,mt ee.mpr yes]
    · intro a _ ne
      have no : etiquetaDeCasilla e a≠j:=by
        intro eq
        apply ne
        exact (incidencia_etiquetada e a).2.symm.trans (congrArg familiaDeReserva eq)
      simp [no]
    · simp
  simp_rw [one]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem integral_discreta_de_cada_fibra {q : ℕ} (qp : 0<q) {m η H b : ℝ}
    (hp : 0<η) (mn : 0≤m) (slack : m≤1-η) (hn : 0≤H) (b1 : 1≤b)
    (use : ℕ→ℝ) (bound : ∀ t<q,use t≤b*(m/q+H*(1-(t:ℝ)/q*m))) :
    -(1-m)*log (1-m)-m-((b-1)*m/q+b*H)*(q*(m/η))≤
      ∑ t∈Finset.range q,(use t*log (1-(t:ℝ)/q*m)) := by
  let z (t : ℕ):=1-(t:ℝ)/q*m
  let K:=(b-1)*m/q+b*H
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have bn : 0≤b:=by linarith
  have bnm : 0≤b-1:=sub_nonneg.mpr b1
  have kn : 0≤K:=by dsimp [K]; positivity
  have per t (ht : t<q) : m/q*log (z t)-K*|log (z t)|≤use t*log (z t):=by
    have a : (t:ℝ)/q≤1:=(div_le_one qr).mpr (by exact_mod_cast ht.le)
    have h:=mul_le_mul_of_nonneg_right a mn
    have nz : 0≤(t:ℝ)/q*m:=by positivity
    have lo : η≤z t:=by dsimp [z]; linarith
    have hi : z t≤1:=by dsimp [z]; linarith
    have lg:=Real.log_nonpos (hp.le.trans lo) hi
    have upper : use t≤m/q+K:=by
      have e:=mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hn hi) bn
      have raw:=bound t ht
      change use t≤b*(m/q+H*z t) at raw
      dsimp only [K]
      rw [mul_add] at raw
      calc use t≤b*(m/q)+b*H:=raw.trans (add_le_add_left e _)
           _ = _:=by ring
    have w:=mul_le_mul_of_nonpos_right upper lg
    rw [abs_of_nonpos lg]; linarith only [w,add_mul (m/q) K (log (z t)),mul_neg K (log (z t))]
  have summed:=Finset.sum_le_sum (s:=Finset.range q) (fun t ht=>per t (Finset.mem_range.mp ht))
  rw [Finset.sum_sub_distrib] at summed
  have cost : (∑ t∈Finset.range q,K*|log (z t)|)≤K*((q:ℝ)*(m/η)):=by
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (costo_temporal_de_la_holgura qp hp mn slack) kn
  have leading:=suma_temporal_de_las_holguras qp mn (by linarith : m<1)
  exact (sub_le_sub leading cost).trans summed
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_de_las_cargas_por_incidencia
#print axioms ArticuloA.Historias.integral_discreta_de_cada_fibra
