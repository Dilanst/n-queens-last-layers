import ErroresLogaritmicosDeMasa
namespace ArticuloA.Perfil
noncomputable section
private theorem diferencia_producto {a b c d A B u v : ℝ}
    (ca : |a|≤A) (cb : |d|≤B) (ea : |a-c|≤u) (eb : |b-d|≤v) :
    |a*b-c*d|≤A*v+B*u := by
  rw [show a*b-c*d=a*(b-d)+d*(a-c) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact add_le_add (mul_le_mul ca eb (abs_nonneg _) ((abs_nonneg _).trans ca))
    (mul_le_mul cb ea (abs_nonneg _) ((abs_nonneg _).trans cb))

theorem cuatro_factores (p q : Fin 4→ℝ) (M d : ℝ)
    (pM : ∀ i,|p i|≤M) (qM : ∀ i,|q i|≤M) (dist : ∀ i,|p i-q i|≤d) :
    |p 0*p 1*p 2*p 3-q 0*q 1*q 2*q 3|≤4*M^3*d := by
  have pp (i j : Fin 4) : |p i*p j|≤M*M := by
    rw [abs_mul]; exact mul_le_mul (pM i) (pM j) (abs_nonneg _) ((abs_nonneg _).trans (pM i))
  have qq (i j : Fin 4) : |q i*q j|≤M*M := by
    rw [abs_mul]; exact mul_le_mul (qM i) (qM j) (abs_nonneg _) ((abs_nonneg _).trans (qM i))
  have e (i j : Fin 4) := diferencia_producto (pM i) (qM j) (dist i) (dist j)
  have h := diferencia_producto (pp 0 1) (qq 2 3) (e 0 1) (e 2 3)
  calc
    _ = |(p 0*p 1)*(p 2*p 3)-(q 0*q 1)*(q 2*q 3)| := by rw [mul_assoc (p 0*p 1),mul_assoc (q 0*q 1)]
    _ ≤ _ := h.trans_eq (by ring)

theorem balance_de_fibra (n ρ b D J u e g E G w : ℝ) (hn : 0<n) (bp : 0<b) (wp : 0<w)
    (dw : w≤D) (rr : 0≤ρ) (r1 : ρ≤1) (vu : 0≤u) (u1 : u≤1)
    (mass : n*D=n*(ρ/b)+e) (euler : b*J=1-u) (be : |e|≤E) (bg : |g|≤G) :
    n*|ρ*(J+g/n)/D+u-1|≤(G+E)/w := by
  have dp := wp.trans_le dw
  have deneq : n*D*(ρ*(J+g/n)/D+u-1)=ρ*g-(1-u)*e := by
    rw [show n*D*(ρ*(J+g/n)/D+u-1)=n*ρ*J+ρ*g-(1-u)*(n*D) by field_simp; ring]
    rw [mass,←euler]; field_simp; ring
  have rhs : |ρ*g-(1-u)*e|≤G+E := by
    apply (abs_sub _ _).trans; rw [abs_mul,abs_mul,abs_of_nonneg rr,abs_of_nonneg (sub_nonneg.mpr u1)]
    exact add_le_add (by simpa using mul_le_mul r1 bg (abs_nonneg _) zero_le_one)
      (by simpa using mul_le_mul (show 1-u≤1 by linarith) be (abs_nonneg _) zero_le_one)
  have val := congrArg abs deneq
  rw [abs_mul,abs_of_pos (mul_pos hn dp)] at val
  apply (le_div_iff₀ wp).mpr
  calc
    _ ≤ n*|ρ*(J+g/n)/D+u-1| * D := mul_le_mul_of_nonneg_left dw (mul_nonneg hn.le (abs_nonneg _))
    _ = _ := by rw [mul_right_comm, val]
    _ ≤ _ := rhs
end
end ArticuloA.Perfil
#print axioms ArticuloA.Perfil.cuatro_factores
#print axioms ArticuloA.Perfil.balance_de_fibra
