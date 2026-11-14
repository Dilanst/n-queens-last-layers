import MasasDelOptimoEnLosIntervalos
import L1DesdeElSoporteVariacional
open Filter Set
open scoped Topology NNReal Interval
namespace ArticuloA.Historias
open Perfil
noncomputable section

structure RamaDensa (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ)
    (κ M L B : ℝ) : Prop where
  kp : 0<κ
  k1 : κ≤1
  m1 : 1≤M
  lp : 0≤L
  euler : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)
  espacio : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L
  cota : ∀ x∈Icc 0 (1/2:ℝ),b x≤B
  extremos : ∀ x∈Icc 0 (1/2:ℝ),(p x).diagonal (-1)=1 ∧ (p x).anti 0=1
  normaliza : ∀ x∈Icc 0 (1/2:ℝ),(∫ t in (0:ℝ)..1,((p x).fila t:ℝ))=1 ∧
    (∫ t in (0:ℝ)..1,((p x).columna t:ℝ))=1

theorem L1_desde_la_familia_canonica {P p b κ M L B} (rama : RamaDensa P p b κ M L B) (K : ℕ)
    (cont : ContinuousWithinAt (fun x => (P x).s) (Icc 0 (1/2:ℝ)) 0)
    (primerOrden : Tendsto (fun n : ℕ => deficit (P 0).s n/(n:ℝ)) atTop (𝓝 0))
    (existe : ∀ᶠ n in atTop,0<count n n) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p ((h:ℝ)/n))) (d n) := by
  refine L1_con_soporte_del_valor K (fun n h => p ((h:ℝ)/n)) (fun n h => b ((h:ℝ)/n))
    b (fun x => (P x).s) κ M L (1/(2*B)) B cont ?_ ?_ primerOrden ?_
  · intro y yp yq
    have hy : y∈Icc 0 (1/2:ℝ) := ⟨yp.le,by linarith⟩
    exact ⟨(rama.euler _ hy).coef,rama.cota _ hy⟩
  · intro y yp yq x xp xq
    have hy : y∈Icc 0 (1/2:ℝ) := ⟨yp.le,by linarith⟩
    have hx : x∈Icc 0 (1/2:ℝ) := ⟨xp.le,xq⟩
    simpa only [Real.coe_toNNReal _ yp.le,Real.coe_toNNReal _ xp.le] using
      soporte_entre_perfiles (rama.euler _ hx) (rama.euler _ hy) (rama.espacio _ hy) (rama.espacio _ hx)
        rama.kp rama.lp (Real.toNNReal_pos.mpr yp)
  · filter_upwards [existe,eventually_ge_atTop 1,eventually_ge_atTop (2*K)] with n sol hn size
    have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have inside (h : ℕ) (hk : h≤K) : (h:ℝ)/n∈Icc 0 (1/2:ℝ) := by
      refine ⟨by positivity,(div_le_iff₀ np).mpr ?_⟩
      have cmp : 2*(h:ℝ)≤n := by exact_mod_cast (by omega : 2*h≤n)
      linarith
    have frac (h : ℕ) : ((h:ℝ)/n).toNNReal=fraccionHuecos n h := by
      apply NNReal.eq
      simp [Real.coe_toNNReal _ (div_nonneg (Nat.cast_nonneg _) np.le),fraccionHuecos]
    have base : (0:ℝ)∈Icc 0 (1/2:ℝ) := by constructor <;> norm_num
    refine ⟨sol,?_,?_,?_⟩
    · intro h hk
      have hx:=inside h hk
      have data := rama.euler _ hx
      rw [frac h] at data
      exact datos_de_cuadratura (by omega) (by omega) data (rama.espacio _ hx) rama.kp rama.k1 rama.m1 rama.lp
        (rama.cota _ hx) (rama.extremos _ hx).1 (rama.extremos _ hx).2 (rama.normaliza _ hx).1 (rama.normaliza _ hx).2
    · have d:=entropia_fisica (rama.euler _ base) (rama.espacio _ base) rama.kp rama.lp
      rw [(rama.euler _ base).masa] at d
      simpa [escalaLog] using d
    · intro h hk hp
      have hx:=inside h hk
      have data:=rama.euler _ hx
      rw [frac h] at data
      have pos : 0<fraccionHuecos n h := div_pos (by exact_mod_cast hp) (by exact_mod_cast (by omega : 0<n))
      have d:=entropia_fisica data (rama.espacio _ hx) rama.kp rama.lp
      simp only [escalaLog,if_neg pos.ne'] at d
      have m : (n:ℝ)*(P ((h:ℝ)/n)).rho=(↑(n-h):ℝ) := by
        rw [data.masa,Nat.cast_sub (by omega : h≤n)]
        simp only [fraccionHuecos,NNReal.coe_div,NNReal.coe_natCast]
        field_simp
      rw [d, mul_sub,←mul_assoc,m]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.L1_desde_la_familia_canonica
