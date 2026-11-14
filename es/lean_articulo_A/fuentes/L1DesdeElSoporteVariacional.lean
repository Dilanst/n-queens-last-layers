import BordeDiadicoDeLaEntropia
import UnaCotaParaTodasLasCapas
open Filter Set
open scoped Topology NNReal
namespace ArticuloA.Historias
open Perfil
noncomputable section

theorem tangente_en_dos_escalas (S a : ℝ→ℝ) (B : ℝ)
    (coef : ∀ y : ℝ,0<y → y≤1/4 → 0<a y ∧ a y≤B)
    (soporte : ∀ y : ℝ,0<y → y≤1/4 → ∀ x : ℝ,0<x → x≤1/2 →
      S x-S y≤(x-y)*Real.log (a y/y^2)) :
    ∀ y : ℝ,0<y → y≤1/4 → S (2*y)-S y≤y*(Real.log B-2*Real.log y) := by
  intro y yp lim
  obtain ⟨pos,ub⟩ := coef y yp lim
  have t := soporte y yp lim (2*y) (by positivity) (by linarith)
  rw [show 2*y-y=y by ring,Real.log_div pos.ne' (pow_ne_zero 2 yp.ne'),Real.log_pow] at t
  exact t.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.log_le_log pos ub) _) yp.le)

theorem L1_con_soporte_del_valor (K : ℕ) (p : ℕ→ℕ→FactoresContinuos) (b : ℕ→ℕ→ℝ) (a S : ℝ→ℝ)
    (κ M L m₀ B : ℝ) (cont : ContinuousWithinAt S (Icc 0 (1/2:ℝ)) 0)
    (coef : ∀ y : ℝ,0<y → y≤1/4 → 0<a y ∧ a y≤B)
    (soporte : ∀ y : ℝ,0<y → y≤1/4 → ∀ x : ℝ,0<x → x≤1/2 →
      S x-S y≤(x-y)*Real.log (a y/y^2))
    (primerOrden : Tendsto (fun n : ℕ => deficit (S 0) n/(n:ℝ)) atTop (𝓝 0))
    (perfil : ∀ᶠ n : ℕ in atTop, 0<count n n ∧
      (∀ h≤K,PerfilKL n h (p n h) κ M L (b n h) m₀) ∧
      S 0=(-Real.log (b n 0)-3)-entropiaDeFactores (p n 0) 1 ∧
      ∀ h≤K,0<h → (n:ℝ)*S ((h:ℝ)/n)=(↑(n-h):ℝ)*(-Real.log (b n h/(fraccionHuecos n h:ℝ)^2)-3)-
        (n:ℝ)*entropiaDeFactores (p n h) (fraccionHuecos n h)) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p n h)) (d n) := by
  let Eb := (K:ℝ)*max (Real.log B+4*Real.log 2) 0
  apply L1_desde_el_perfil K p b (fun n h => S ((h:ℝ)/n)) κ M L m₀ (S 0) Eb primerOrden
  filter_upwards [perfil,eventually_ge_atTop 1,eventually_ge_atTop (2*K)] with n data hn size
  obtain ⟨sol,samples,full,euler⟩ := data
  refine ⟨sol,samples,full,euler,?_,mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)⟩
  intro h hk _
  exact borde_para_K_fijo S _ cont (tangente_en_dos_escalas S a B coef soporte) n h K (by omega) hk size
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tangente_en_dos_escalas
#print axioms ArticuloA.Historias.L1_con_soporte_del_valor
