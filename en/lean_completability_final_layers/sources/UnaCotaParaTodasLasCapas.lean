import TresCotasDelPerfilFisico
open Filter
open scoped Topology NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2
noncomputable section

def fraccionHuecos (n h : ℕ) : ℝ≥0 := (h:ℝ≥0)/(n:ℝ≥0)
def coloresDelPerfil (n h : ℕ) (p : FactoresContinuos) :=
  if h=0 then coloresLlenos n (pesosMalla n 1 p) else sameColors (pesosMalla n (fraccionHuecos n h) p)

structure EntradasDeCapas (n K : ℕ) (p : ℕ→FactoresContinuos) (b s : ℕ→ℝ) (κ M L m₀ s₁ Eb : ℝ) : Prop where
  datos : ∀ h≤K,PerfilKL n h (p h) κ M L (b h) m₀
  lleno : s₁=(-Real.log (b 0)-3)-entropiaDeFactores (p 0) 1
  euler : ∀ h≤K,0<h → (n:ℝ)*s h=(↑(n-h):ℝ)*(-Real.log (b h/(fraccionHuecos n h:ℝ)^2)-3)-
    (n:ℝ)*entropiaDeFactores (p h) (fraccionHuecos n h)
  borde : ∀ h≤K,0<h → (n:ℝ)*(s h-s₁)≤2*h*Real.log n+Eb
  margen : 0≤Eb

def deficit (s₁ : ℝ) (n : ℕ) := max (n*Real.log n+n*s₁-Real.log (count n n)) 0
def costeUniforme (K : ℕ) (κ M L m₀ s₁ Eb : ℝ) (n : ℕ) :=
  deficit s₁ n+(4+(4+60*amplitudPerfil κ M)*(ultimoRango n:ℝ))+
    (errorPerfil κ M L m₀+Eb+K*Real.log 2+2*Real.log K.factorial)

theorem presupuesto_mayorado (n K h : ℕ) (hn : 2≤n) (hk : h≤K) (κ M L m₀ s₁ Eb E : ℝ) (he : E≤Eb) :
    presupuesto n h hn κ M L m₀ s₁ E≤costeUniforme K κ M L m₀ s₁ Eb n := by
  have h1 : (h:ℝ)≤K := by exact_mod_cast hk
  have h2 : Real.log h.factorial≤Real.log K.factorial :=
    Real.log_le_log (by exact_mod_cast Nat.factorial_pos h) (by exact_mod_cast Nat.factorial_le hk)
  have h3 := mul_le_mul_of_nonneg_right h1 (show 0≤Real.log 2 by exact Real.log_nonneg (by norm_num))
  have d := le_max_left (n*Real.log n+n*s₁-Real.log (count n n)) (0:ℝ)
  unfold presupuesto costeUniforme deficit restoRango ultimoRango
  rw [dif_pos hn]
  linarith only [h2,h3,he,d]

theorem uniforme_en_los_niveles {n K p b s κ M L m₀ s₁ Eb} (src : EntradasDeCapas n K p b s κ M L m₀ s₁ Eb)
    (hn : 2≤n) (size : 2*K≤n) (sol : 0<count n n) (h : ℕ) (hk : h≤K) :
    Tres n h (coloresDelPerfil n h (p h)) (costeUniforme K κ M L m₀ s₁ Eb n) := by
  by_cases zero : h=0
  · subst h
    rw [coloresDelPerfil,if_pos rfl]
    exact (comparacion_del_perfil_lleno (src.datos _ hk) hn sol s₁ src.lleno).aumentar
      (presupuesto_mayorado _ _ _ hn hk _ _ _ _ _ _ _ src.margen)
  · rw [coloresDelPerfil,if_neg zero]
    have hp : 0<h := Nat.pos_of_ne_zero zero
    have np : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have nnp : 0<(n:ℝ≥0) := by exact_mod_cast (by omega : 0<n)
    have xp : 0<fraccionHuecos n h := div_pos (by exact_mod_cast hp) nnp
    have x1 : (fraccionHuecos n h:ℝ)≤1 := by
      simp only [fraccionHuecos,NNReal.coe_div,NNReal.coe_natCast]
      exact (div_le_one np).mpr (by exact_mod_cast (by omega : h≤n))
    have cuota : (fraccionHuecos n h:ℝ)*(n:ℝ)=(h:ℝ) := by
      simp only [fraccionHuecos,NNReal.coe_div,NNReal.coe_natCast,div_mul_cancel₀ _ np.ne']
    exact (comparacion_del_perfil_con_huecos (src.datos h hk) hn (by omega) sol _ xp x1 cuota
      (s h) s₁ Eb (src.euler h hk hp) (src.borde h hk hp)).aumentar
      (presupuesto_mayorado _ _ _ hn hk _ _ _ _ _ _ _ le_rfl)

theorem coste_uniforme_sublineal (K : ℕ) (κ M L m₀ s₁ Eb : ℝ)
    (primerOrden : Tendsto (fun n : ℕ => deficit s₁ n/(n:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => costeUniforme K κ M L m₀ s₁ Eb n/(n:ℝ)) atTop (𝓝 0) := by
  have a := (primerOrden.add (resto_es_sublineal (amplitudPerfil κ M))).add
    (tendsto_const_div_atTop_nhds_zero_nat (errorPerfil κ M L m₀+Eb+K*Real.log 2+2*Real.log K.factorial))
  simpa only [costeUniforme,add_div,zero_add] using a

theorem L1_desde_el_perfil (K : ℕ) (p : ℕ→ℕ→FactoresContinuos) (b s : ℕ→ℕ→ℝ) (κ M L m₀ s₁ Eb : ℝ)
    (primerOrden : Tendsto (fun n : ℕ => deficit s₁ n/(n:ℝ)) atTop (𝓝 0))
    (perfil : ∀ᶠ n : ℕ in atTop, 0<count n n ∧ EntradasDeCapas n K (p n) (b n) (s n) κ M L m₀ s₁ Eb) :
    ∃ d : ℕ→ℝ,Tendsto (fun n : ℕ => d n/(n:ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p n h)) (d n) := by
  refine ⟨_,coste_uniforme_sublineal K κ M L m₀ s₁ Eb primerOrden,?_⟩
  filter_upwards [perfil,eventually_ge_atTop 2,eventually_ge_atTop (2*K)] with n hs hn hk
  exact uniforme_en_los_niveles hs.2 hn hk hs.1
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.L1_desde_el_perfil
