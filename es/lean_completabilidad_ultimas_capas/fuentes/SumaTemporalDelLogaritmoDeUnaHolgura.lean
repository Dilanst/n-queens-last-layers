import EntropiaDeLasHolgurasDeLinea
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem diferencia_de_una_holgura_positiva {z w : ℝ} (zp : 0<z) (wp : 0<w) :
    z*log z-z-(w*log w-w)≤(z-w)*log z := by
  have eq:=Real.log_le_sub_one_of_pos (div_pos zp wp)
  rw [Real.log_div zp.ne' wp.ne'] at eq
  have h:=mul_le_mul_of_nonneg_right eq wp.le
  simp only [sub_mul,div_mul_cancel₀ _ wp.ne',one_mul] at h
  linarith only [h,sub_mul (log z) (log w) w,sub_mul z w (log z),mul_comm (log z) w,mul_comm (log w) w]

theorem suma_temporal_de_las_holguras {q : ℕ} (qp : 0<q) {m : ℝ} (mn : 0≤m) (m1 : m<1) :
    -(1-m)*log (1-m)-m ≤ ∑ t∈Finset.range q,(m/q*log (1-(t:ℝ)/q*m)) := by
  let z (t : ℕ):=1-(t:ℝ)/q*m
  let F (t : ℕ):=z t*log (z t)-z t
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have pos t (tq : t≤q) : 0<z t:=by
    have a : (t:ℝ)/q≤1:=(div_le_one qr).mpr (by exact_mod_cast tq)
    have h:=mul_le_mul_of_nonneg_right a mn
    dsimp [z]; linarith
  have per t (tq : t<q) : F t-F (t+1)≤m/q*log (z t):=by
    have h:=diferencia_de_una_holgura_positiva (pos t tq.le) (pos _ tq)
    have dif : z t-z (t+1)=m/q:=by dsimp [z]; push_cast; ring
    rwa [dif] at h
  have sum:=Finset.sum_le_sum (s:=Finset.range q) (fun t ht=>per t (Finset.mem_range.mp ht))
  have tel : (∑ t∈Finset.range q,(F t-F (t+1)))=F 0-F q:=by
    have e:=Finset.sum_range_sub F q
    rw [←neg_inj,←Finset.sum_neg_distrib] 
    simpa only [neg_sub] using e
  rw [tel] at sum
  have z0 : z 0=1:=by simp [z]
  have zq : z q=1-m:=by simp [z,qr.ne']
  dsimp only [F] at sum
  rw [z0,zq,Real.log_one] at sum
  change _≤∑ t∈Finset.range q,(m/q*log (z t))
  linarith only [sum]

theorem costo_temporal_de_la_holgura {q : ℕ} (qp : 0<q) {η m : ℝ} (hp : 0<η) (mn : 0≤m)
    (slack : m≤1-η) : (∑ t∈Finset.range q,|log (1-(t:ℝ)/q*m)|)≤(q:ℝ)*(m/η) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have per (t : ℕ) (ht : t<q) : |log (1-(t:ℝ)/q*m)|≤m/η:=by
    let z:=1-(t:ℝ)/q*m
    have a : (t:ℝ)/q≤1:=(div_le_one qr).mpr (by exact_mod_cast ht.le)
    have mul:=mul_le_mul_of_nonneg_right a mn
    have nz : 0≤(t:ℝ)/q*m:=by positivity
    have lo : η≤z:=by dsimp [z]; linarith
    have hi : z≤1:=by dsimp [z]; linarith
    have zp:=hp.trans_le lo
    have lg:=Real.log_le_sub_one_of_pos (one_div_pos.mpr zp)
    rw [Real.log_div one_ne_zero zp.ne',Real.log_one,zero_sub] at lg
    change |log z|≤_
    rw [abs_of_nonpos (Real.log_nonpos zp.le hi)]
    apply lg.trans
    have eq : 1/z-1=(1-z)/z:=by field_simp
    rw [eq]
    apply div_le_div₀ mn _ hp lo
    dsimp [z]; linarith
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
    (Finset.sum_le_sum (s:=Finset.range q) (fun t ht=>per t (Finset.mem_range.mp ht)))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_temporal_de_las_holguras
#print axioms ArticuloA.Historias.costo_temporal_de_la_holgura
