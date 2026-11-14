import CompararDosPerfilesPorSuCuadratura
import DelBlancoDeMallaAlPerfilContinuo
open Set Filter
open scoped NNReal Topology
namespace ArticuloA.Historias
open Perfil
noncomputable section

/-- The endpoint input of Appendix A2, on the four actual spatial intervals.
The density parameter x is distinct from the coordinates of a cross. -/
def ContinuidadEnElLleno (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ d : ℝ,0<d ∧ ∀ x∈Icc (0:ℝ) (1/2:ℝ),x<d →
    |b x-b 0|≤ε ∧ CercaniaDeFactores (p x) (p 0) ε

def aDelLleno {n} (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (z : Cell n) :=
  perfilDirectoContinuo (p 0) (b 0) (medio n z.1.val) (medio n z.2.val)

theorem malla_converge_al_lleno {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b) (cont : ContinuidadEnElLleno p b) (h : ℕ) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,∀ z : Cell n,
       |blancoNormalizado h (p ((h:ℝ)/n)) z-aDelLleno p b z|≤ε := by
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama pt
  let lo:ℝ≥0:=⟨κ,rama.kp.le⟩
  let hi:ℝ≥0:=⟨M,zero_le_one.trans rama.m1⟩
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have bpos := (rama.euler 0 zero).coef
  have bp : 0<B := bpos.trans_le (rama.cota 0 zero)
  have mp : 0≤M := zero_le_one.trans rama.m1
  have lp:=rama.lp
  let K:=4*M^3*C+4*(M^4/κ^4)*M^4+B*(2*(4*M^3*L)*M^4+2*(8*M^7*L))
  let V:=B*(8*M^7)+M^8
  intro ε ep
  have vp : 0<V+1 := by dsimp [V]; positivity
  let a:=ε/2/(V+1)
  have ap : 0<a := div_pos (half_pos ep) vp
  obtain ⟨d,dp,close⟩:=cont a ap
  obtain ⟨N,big⟩:=exists_nat_gt (2*(C:ℝ)/κ)
  have sm:= (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat K)).2 (ε/2) (half_pos ep)
  have den:= (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat (h:ℝ))).2 d dp
  filter_upwards [sm,den,bal h,eventually_ge_atTop (2*h+2),eventually_ge_atTop N] with n err den bal nh nb
  intro z
  have nr : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  let x:ℝ:=(h:ℝ)/n
  have xp : 0≤x := by dsimp [x]; positivity
  have hx : x∈Icc 0 (1/2:ℝ) := by
    refine ⟨xp,(div_le_iff₀ nr).mpr ?_⟩
    have t : 2*(h:ℝ)≤n := by exact_mod_cast (by omega : 2*h≤n)
    linarith
  have E:=rama.euler x hx
  have mass:=integral_masa_cuadrada E
  rw [E.masa,Real.coe_toNNReal _ xp] at mass
  have q : 1-x=(↑(n-h):ℝ)/n := by rw [Nat.cast_sub (by omega : h≤n)]; dsimp [x]; field_simp
  rw [q] at mass
  have margin : 2*(C:ℝ)≤κ*n := by
    have lim : 2*(C:ℝ)/κ≤n := big.le.trans (by exact_mod_cast nb)
    simpa only [mul_comm] using (div_le_iff₀ rama.kp).mp lim
  have first:=malla_al_continuo_en_la_misma_densidad (κ:=lo) (m:=hi) (by omega : 2≤n)
    (rama.espacio x hx) (show 0<lo from rama.kp) (show 1≤hi from rama.m1) lp E.coef bal margin mass z
  have approx : |blancoNormalizado h (p x) z-perfilDirectoContinuo (p x) (b x) (medio n z.1.val) (medio n z.2.val)|≤K/n := by
    apply first.trans
    apply div_le_div_of_nonneg_right _ nr.le
    exact add_le_add_left (mul_le_mul_of_nonneg_right (rama.cota _ hx) (by positivity)) _
  obtain ⟨bc,pc⟩:=close x hx den
  have second:=comparar_dos_perfiles (rama.espacio x hx) (rama.espacio 0 zero) rama.kp.le lp E.coef.le
    bpos.le pc (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
  have rest : b x*(8*M^7*a)+M^8*|b x-b 0|≤ε/2 := by
    calc _ ≤ B*(8*M^7*a)+M^8*a := add_le_add (mul_le_mul_of_nonneg_right (rama.cota x hx) (by positivity))
                 (mul_le_mul_of_nonneg_left bc (by positivity))
         _ = V*a := by dsimp [V]; ring
         _ ≤ (V+1)*a := mul_le_mul_of_nonneg_right (by linarith) ap.le
         _ = _ := by dsimp only [a]; field_simp; ring
  exact (abs_sub_le _ _ _).trans ((add_le_add (approx.trans err.le) (second.trans rest)).trans_eq (by ring))

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.malla_converge_al_lleno
