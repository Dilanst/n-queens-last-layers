import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open scoped BigOperators
noncomputable section

private theorem paso_de_la_envolvente {D d a : ℝ} (dp : 0<d) (eq : D=d+a) (a0 : 0≤a) (a9 : 9≤12*a) :
    1+9/D≤(D/d)^12 := by
  have Dp : 0<D:=by linarith
  have order : 9/D≤(12*a)/d := (div_le_div_iff₀ Dp dp).mpr (by
    calc
      9*d ≤ (12*a)*d := mul_le_mul_of_nonneg_right a9 dp.le
      _ ≤ (12*a)*D := mul_le_mul_of_nonneg_left (by linarith only [eq,a0]) (by positivity))
  have lin:=one_add_mul_le_pow (a:=a/d) (by have q:=div_nonneg a0 dp.le; linarith) 12
  have ratio : D/d=1+a/d:=by rw [eq,add_div,div_self dp.ne']
  rw [ratio]
  push_cast at lin
  rw [mul_div_assoc] at order
  exact (add_le_add_left order 1).trans lin

/-- Stopped form: the drift inequality is needed only up to time t. -/
theorem envolvente_de_seguimiento_hasta_la_parada {q t : ℕ} {η A : ℝ} (qp : 0<q) (tq : t≤q)
    (hp : 0<η) (hq : η≤1/4) (ap : 0≤A) (X : ℕ→ℝ)
    (rec : ∀ j≤t,X j≤A+∑ s∈Finset.range j,(9/((q:ℝ)-(1-η)*s))*X s) :
    X t ≤ A*(1/η)^12 := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  let a:=1-η
  let D (s : ℕ):=(q:ℝ)-a*s
  let B (j : ℕ):=A+∑ s∈Finset.range j,9/D s*X s
  have a0 : 0≤a:=by dsimp [a]; linarith only [hq]
  have a9 : 9≤12*a:=by dsimp [a]; linarith only [hq]
  have low (s : ℕ) (sq : s≤q) : η*q≤D s := by
    have ub:=mul_le_mul_of_nonneg_left (show (s:ℝ)≤q by exact_mod_cast sq) a0
    dsimp [D,a] at *
    linarith only [ub]
  have pos (s : ℕ) (sq : s≤q) : 0<D s := (mul_pos hp qr).trans_le (low s sq)
  have bound (j : ℕ) (jt : j≤t) : B j≤A*((q:ℝ)/D j)^12 := by
    induction j with
    | zero => simp [B,D,qr.ne']
    | succ j ih =>
      have prev:=ih (by omega)
      have p:=pos j (by omega)
      have next:=pos (j+1) (by omega)
      have eq : D j=D (j+1)+a := by dsimp [D]; push_cast; ring
      have inc:=paso_de_la_envolvente next eq a0 a9
      have rx : X j≤B j:=rec j (by omega)
      have fac : 0≤1+9/D j := by positivity
      have amp : 0≤A*((q:ℝ)/D j)^12 := by positivity
      calc
        B (j+1) = B j+9/D j*X j := by simp [B,Finset.sum_range_succ,add_assoc]
        _ ≤ B j+9/D j*B j := by gcongr
        _ = B j*(1+9/D j) := by ring
        _ ≤ (A*((q:ℝ)/D j)^12)*(D j/D (j+1))^12 := mul_le_mul prev inc fac amp
        _ = A*((q:ℝ)/D (j+1))^12 := by
          rw [mul_assoc,←mul_pow]; congr 2; field_simp
  have f : (q:ℝ)/D t≤1/η:=(div_le_div_iff₀ (pos _ tq) hp).mpr (by linarith only [low t tq])
  exact (rec t le_rfl).trans ((bound t le_rfl).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg qr.le (pos t tq).le) f 12) ap))
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.envolvente_de_seguimiento_hasta_la_parada
