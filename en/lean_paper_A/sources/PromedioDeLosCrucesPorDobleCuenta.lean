import MediasFisicasDesdeUnCentroConvergente
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Limites Filter Set
open scoped Topology
theorem reponderacion_de_una_prueba_acotada {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h)
    (t : (n : ℕ)→Cell n→ℝ) (T : ℝ) (tp : 0<T) (bound : ∀ n z,|t n z|≤T) :
    Tendsto (fun n => promedioNivel n (n-h) (fun Q => mediaCruces Q h (t n))-
      mediaD n h (fun z => t n z/aDelLleno p b z)) atTop (𝓝 0) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  let m:=b 0*κ^8
  have mp : 0<m := mul_pos (rama.euler 0 zero).coef (pow_pos rama.kp _)
  have low (n) (z : Cell n) : m≤aDelLleno p b z := piso_integral_del_cruce (rama.espacio 0 zero)
    rama.kp rama.lp (rama.euler 0 zero).coef (medio_admisible z.1.isLt) (medio_admisible z.2.isLt)
  let w:=fun (n : ℕ) (z : Cell n) => t n z/aDelLleno p b z
  have cap (n z) : |w n z|≤T/m := by
    dsimp only [w]; rw [abs_div,abs_of_pos (mp.trans_le (low n z))]
    exact div_le_div₀ tp.le (bound n z) mp (low n z)
  let X:=fun n (Q : Placement n) => mediaCruces Q h (t n)-Dobs n h (w n) Q
  have boundX : ∀ᶠ n : ℕ in atTop,∀ Q∈nivel n (n-h),|X n Q|≤T+T/m := by
    filter_upwards [eventually_ge_atTop h] with n nh
    intro Q mem
    have pair := (Finset.mem_filter.mp mem).2
    have card:=numero_cruces Q pair.1
    rw [pair.2,show n-(n-h)=h by omega] at card
    have hpos : 0<(h:ℝ)^2 := by positivity
    have capT : |mediaCruces Q h (t n)|≤T := by
      rw [mediaCruces,abs_div,abs_of_pos hpos]
      apply (div_le_iff₀ hpos).mpr
      exact (Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum (fun z _ => bound n z)).trans_eq
        (by simp [card,nsmul_eq_mul,mul_comm]))
    exact (abs_sub ..).trans (add_le_add capT (directa_acotada n h nh hh _ _ (div_nonneg tp.le mp.le) (cap n) Q mem))
  have dir:=(directa_del_articulo rama (euler_puntual_de_la_rama rama) cont first h hh).1
  have dev (ε : ℝ) (ep : 0<ε) : Tendsto (fun n => desviacion n (n-h) (X n) 0 ε) atTop (𝓝 0) := by
    let η:=ε*m/T
    have ηp : 0<η := div_pos (mul_pos ep mp) tp
    apply squeeze_zero' _ _ (dir η ηp)
    · apply Eventually.of_forall; intro n; unfold desviacion
      apply Finset.sum_nonneg; intro _ _; split <;> positivity
    · filter_upwards [eventually_ge_atTop h] with n nh
      unfold desviacion probCruceMalo; apply Finset.sum_le_sum; intro Q mem
      have pair := (Finset.mem_filter.mp mem).2
      by_cases bad : ∃ z∈cruces Q,η< |(crossDegree (n-h) Q z:ℝ)/n-aDelLleno p b z|
      · rw [if_pos bad]; split <;> first | exact le_rfl | positivity
      · have good z (hz : z∈cruces Q) : |(crossDegree (n-h) Q z:ℝ)/n-aDelLleno p b z|≤η :=
          le_of_not_gt (fun gt => bad ⟨z,hz,gt⟩)
        have cmp:=error_reponderado Q h hh nh pair.1 pair.2 _ _ m T η mp (low n) (bound n) good
        have ok : |X n Q-0|≤ε := by
          rw [sub_zero,show X n Q=mediaCruces Q h (t n)-Dobs n h (w n) Q by rfl,abs_sub_comm]
          exact cmp.trans_eq (by dsimp [η]; field_simp; ring)
        simp only [bad,if_false,if_neg (not_lt_of_ge ok),le_refl]
  have mean:=media_desde_prob (fun n => n-h) X 0 (T+T/m)
    ((niveles_de_una_reparacion first h hh).mono (fun _ v => v.1)) boundX dev
  apply mean.congr; intro n
  rw [directa_uniforme]; unfold promedioNivel
  simp only [X,Dobs,w,Finset.sum_sub_distrib,sub_div]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.reponderacion_de_una_prueba_acotada
