import EntropiaDeLaCasillaDesdeLaMarcaSeguida
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem log_factorial_superior_para_el_camino (q : ℕ) (qp : 0<q) :
    log (q.factorial:ℝ)≤(q:ℝ)*log q-q+1+log q := by
  induction q with
  | zero=>omega
  | succ k ih=>
    rcases k with _|r
    · norm_num
    · let m : ℕ:=r+1
      have mp : 0<(m:ℝ):=by dsimp [m]; positivity
      have child : 0<(m:ℝ)+1:=by positivity
      have step:=Real.log_le_sub_one_of_pos (div_pos mp child)
      rw [Real.log_div mp.ne' child.ne'] at step
      have b:=mul_le_mul_of_nonneg_right step child.le
      rw [sub_mul,sub_mul,div_mul_cancel₀ _ child.ne',one_mul] at b
      have prev:=ih (by omega)
      change log (m.factorial:ℝ)≤(m:ℝ)*log m-m+1+log m at prev
      change log ((m+1).factorial:ℝ)≤((m+1:ℕ):ℝ)*log ((m+1:ℕ):ℝ)-((m+1:ℕ):ℝ)+1+log ((m+1:ℕ):ℝ)
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Real.log_mul child.ne' (by positivity)]
      nlinarith only [prev,b]

theorem cota_superior_de_la_base_por_celda {n q : ℕ} (np : 0<n) (qp : 0<q) (v : Cell n→ℝ≥0)
    (mass : (∑ e,(v e:ℝ))=q) :
    log (q:ℝ)-(∑ e,(v e:ℝ)*log (v e:ℝ))/q≤2*log n := by
  have nr : 0<(n:ℝ):=by exact_mod_cast np
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  let u:=(q:ℝ)/(n:ℝ)^2
  have up : 0<u:=div_pos qr (sq_pos_of_pos nr)
  have per e : (v e:ℝ)*(log u-log (v e:ℝ))≤u-(v e:ℝ):=by
    by_cases zero : v e=0
    · simp [zero,up.le]
    have pos : 0<(v e:ℝ):=by exact_mod_cast pos_iff_ne_zero.mpr zero
    have lg:=Real.log_le_sub_one_of_pos (div_pos up pos)
    rw [Real.log_div up.ne' pos.ne'] at lg
    have a:=mul_le_mul_of_nonneg_right lg pos.le
    rw [sub_mul,sub_mul,div_mul_cancel₀ _ pos.ne',one_mul] at a
    nlinarith only [a]
  have one : (∑ _e : Cell n,u)=(q:ℝ):=by
    simp [Cell,u,Fintype.card_prod,nsmul_eq_mul,pow_two]; field_simp
  have s:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>per e)
  simp_rw [mul_sub] at s
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,mass,one,sub_self] at s
  have lg : log u=log (q:ℝ)-2*log n:=by dsimp [u]; rw [Real.log_div qr.ne' (pow_ne_zero _ nr.ne'),Real.log_pow]; norm_num
  rw [lg] at s
  have raw : (q:ℝ)*(log q-2*log n)≤∑ e,(v e:ℝ)*log (v e:ℝ):=by linarith only [s]
  have bd : log (q:ℝ)-2*log n≤(∑ e,(v e:ℝ)*log (v e:ℝ))/q:=(le_div_iff₀ qr).mpr (by simpa only [mul_comm (log (q:ℝ)-2*log n)] using raw)
  linarith only [bd]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.log_factorial_superior_para_el_camino
#print axioms ArticuloA.Historias.cota_superior_de_la_base_por_celda
