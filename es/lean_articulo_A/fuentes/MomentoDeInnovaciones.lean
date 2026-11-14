import EsperanzaRealFinita
noncomputable section
namespace ArticuloA.RealFinita.Momento
open ArticuloA.Trayectoria ArticuloA.Trayectoria.ProfileKernel
open scoped NNReal

structure Exponencial where
  fn : ℝ → ℝ
  zero : fn 0 = 1
  add : ∀ x y, fn (x+y) = fn x * fn y
  pos : ∀ x, 0 < fn x
  mono : Monotone fn
  arriba : ∀ x, x+1 ≤ fn x
  cuadratico : ∀ {x}, |x| ≤ 1 → fn x - 1 - x ≤ x^2
variable (E : Exponencial)

def expMas (z : ℝ) : ℝ≥0 := ⟨E.fn z,(E.pos _).le⟩
variable {X : Type}

theorem mgf_fila (row : Atoms ℝ≥0 X) (norm : total masas row = 1)
    (D : X → ℝ) (centro : media row D = 0) (θ B : ℝ) (pos : 0 ≤ θ)
    (small : θ*B ≤ 1) (bound : ∀ i ∈ row, |D i.2| ≤ B) :
    media row (fun y => E.fn (θ*D y)) ≤ E.fn ((θ*B)^2) := by
  have h := media_mono row (fun y => E.fn (θ*D y))
    (fun y => (1+(θ*B)^2)+θ*D y) (by
      intro i hi
      have h1 : |θ*D i.2| ≤ θ*B := by
        rw [abs_mul,abs_of_nonneg pos]; exact mul_le_mul_of_nonneg_left (bound i hi) pos
      have h2 := E.cuadratico (h1.trans small)
      have h3 := mul_self_le_mul_self (abs_nonneg _) h1
      rw [←sq, sq_abs, ←sq] at h3
      change E.fn (θ*D i.2) ≤ 1+(θ*B)^2+θ*D i.2
      linarith only [h2,h3])
  rw [media_affine,norm,centro] at h
  change _ ≤ (1:ℝ)*(1+(θ*B)^2)+θ*0 at h
  simp only [one_mul,mul_zero,add_zero] at h
  exact h.trans (by simpa only [add_comm (1:ℝ)] using E.arriba ((θ*B)^2))

theorem cola (step : Nat → X → Atoms ℝ≥0 X) (M : Nat → X → ℝ)
    (norm : ∀ t x, total masas (step t x) = 1)
    (center : ∀ t x, media (step t x) (fun y => M (t+1) y - M t x) = 0)
    (θ B : ℝ) (pos : 0 ≤ θ) (small : θ*B ≤ 1)
    (bound : ∀ t x i, i ∈ step t x → |M (t+1) i.2 - M t x| ≤ B)
    (t m : Nat) (x : X) (a : ℝ) :
    (avg masas (leaves masas step t m x) (mark masas (fun y => a ≤ M (t+m) y))).val ≤
      E.fn ((m:ℝ)*(θ*B)^2 + θ*M t x - θ*a) := by
  let H := fun u y => expMas E (θ*M u y)
  let L := expMas E ((θ*B)^2)
  let b := expMas E (-(θ*a))
  have row (u : Nat) (v : X) : masas.le (avg masas (step u v) (H (u+1))) (masas.mul L (H u v)) := by
    change (avg masas _ _).val ≤ E.fn _ * E.fn _
    rw [←media_coe]
    have id (y : X) : (H (u+1) y:ℝ) = 0 + E.fn (θ*M u v)*E.fn (θ*(M (u+1) y - M u v)) := by
      change E.fn _ = _; rw [zero_add,←E.add]; congr 1; ring
    simp_rw [id]
    rw [media_affine,mul_zero,zero_add,mul_comm (E.fn ((θ*B)^2))]
    exact mul_le_mul_of_nonneg_left
      (mgf_fila E _ (norm u v) _ (center u v) _ _ pos small (bound u v)) (E.pos _).le
  have bad (i) (_ : i ∈ leaves masas step t m x) (h : a ≤ M (t+m) i.2) :
      masas.le masas.one (masas.mul b (H (t+m) i.2)) := by
    change 1 ≤ E.fn _ * E.fn _
    rw [←E.add, ←E.zero]; apply E.mono
    linarith [mul_le_mul_of_nonneg_left h pos]
  have tail := leaf_tail masas step H (fun y => a ≤ M (t+m) y) L b row t m x bad
  have pot (j : Nat) : (power masas L j).val = E.fn ((j:ℝ)*(θ*B)^2) := by
    induction j with
    | zero => simpa [power,masas] using E.zero.symm
    | succ j ih =>
      change (power masas L j).val*E.fn _ = _
      rw [ih,←E.add,Nat.cast_succ]; congr 1; ring
  change (avg masas _ _).val ≤ E.fn _ * ((power masas L m).val*E.fn _) at tail
  rw [pot,←E.add,←E.add] at tail
  convert tail using 2; ring
end ArticuloA.RealFinita.Momento
#print axioms ArticuloA.RealFinita.Momento.mgf_fila
#print axioms ArticuloA.RealFinita.Momento.cola
