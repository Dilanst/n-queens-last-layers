import UnaCotaParaTodasLasCapas
open Filter
open scoped Topology
namespace ArticuloA.Historias
noncomputable section

def CotaDePrimerOrden (s : ℝ) := ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
  (n:ℝ)*Real.log n+(n:ℝ)*s-(n:ℝ)*ε≤Real.log (count n n)

theorem sublineal_de_tolerancias {s} (src : CotaDePrimerOrden s) :
    Tendsto (fun n : ℕ => deficit s n/(n:ℝ)) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro a ha; apply Filter.Eventually.of_forall; intro n
    exact ha.trans_le (div_nonneg (le_max_right _ _) (Nat.cast_nonneg _))
  · intro a ha
    filter_upwards [src (a/2) (by positivity),eventually_ge_atTop 1] with n cmp hn
    have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have up : deficit s n≤(n:ℝ)*(a/2) := by
      unfold deficit; apply max_le; linarith; positivity
    have small : deficit s n/(n:ℝ)≤a/2 := (div_le_iff₀ np).mpr (by simpa only [mul_comm] using up)
    exact small.trans_lt (by linarith)

theorem soluciones_eventuales_del_primer_orden {s} (src : CotaDePrimerOrden s) :
    ∀ᶠ n : ℕ in atTop,0<count n n := by
  have l : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [src 1 zero_lt_one,l.eventually (eventually_ge_atTop (2-s)),eventually_ge_atTop 1] with n bd ln hn
  have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  by_contra! z
  have zero : count n n=0 := by omega
  rw [zero,Nat.cast_zero,Real.log_zero,mul_one] at bd
  have pos := mul_pos np (show 0<Real.log (n:ℝ)+s-1 by linarith)
  linarith
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.sublineal_de_tolerancias
#print axioms ArticuloA.Historias.soluciones_eventuales_del_primer_orden
