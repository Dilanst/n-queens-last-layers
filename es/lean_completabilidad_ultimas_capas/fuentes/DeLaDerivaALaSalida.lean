import SalidaSobreTrayectoriasE2
namespace ArticuloA.RealFinita
open scoped NNReal BigOperators
open Trayectoria Trayectoria.ProfileKernel Trayectoria.Adjunto Corte Trayectoria.E2 E2.Regular
noncomputable section
open Classical
theorem salida_por_deriva {n : ℕ} (hn : n≠0) (v : Cell n→ℝ≥0) (w : ColorWeights ℝ≥0)
    (halt : ℕ→State n→Bool) (x : ℕ×State n) (T : ℕ) (M H : ℝ≥0) (cap : ∀ e,v e≤M)
    (line : ∀ t (y : State n),halt t y=false → ∀ f j,j<2*n-1 → y.active f j → w f j≤H)
    (θ g L umbral : ℝ) (tp : 0≤θ) (small : θ*limiteSalto M H≤1) (g0 : 0≤g) (L0 : 0≤L)
    (margin : (g+1)*Real.exp (T*L)<umbral) (bad : List (ℕ×State n)→Prop)
    (tracking : ∀ atom∈rutas (pasoParado w halt) 0 T x,bad atom.2 →
      ∃ (s : ℕ) (E : ℕ→ℝ) (D : Activa n→ℕ→ℝ),s≤T ∧ umbral≤E s ∧
        (∀ c t,t<s → |D c t|≤L*(E t+1)) ∧
        (∀ t≤s,∃ c : Activa n,E t ≤ |ruidoE2 v w halt x (coordenada c) t atom.2+∑ j∈Finset.range t,D c j|)) :
    (avg masas (rutas (pasoParado w halt) 0 T x) (mark masas bad)).val ≤
      (6+4*(↑(2*n-1):ℝ))*(T+1)*(2*Real.exp (T*(θ*limiteSalto M H)^2-θ*g)) := by
  apply salida_con_testigo hn v w halt x T M H cap line θ g tp small bad
  intro atom mem yes
  obtain ⟨s,E,D,st,large,drift,decomp⟩ := tracking atom mem yes
  obtain ⟨c,t,ts,violation⟩ := Seguimiento.ruido_en_primera_salida E D
    (fun c t => ruidoE2 v w halt x (coordenada c) t atom.2) s T st g L umbral g0 L0 margin drift decomp large
  exact ⟨c,t,ts.trans st,violation⟩

theorem exponente_hasta_el_corte (B α : ℝ) (bp : 0<B) (ap : 0<α) :
    ∃ θ c : ℝ,0<θ ∧ 0<c ∧ θ*B≤1 ∧
      ∀ n T : ℕ,T≤2*n → T*(θ*B)^2-θ*(α*n)≤ -(c*n) := by
  let θ := min (1/B) (α/(4*B^2))
  have p : 0<θ := lt_min (by positivity) (by positivity)
  have b : θ*B≤1 := (le_div_iff₀ bp).mp (min_le_left _ _)
  have a : θ*(4*B^2)≤α := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨θ,θ*α/2,p,by positivity,b,?_⟩
  intro n T time
  have t : (T:ℝ)≤2*n := by exact_mod_cast time
  have m := mul_le_mul_of_nonneg_right t (sq_nonneg (θ*B))
  have e := mul_le_mul_of_nonneg_left a (show 0≤θ*(n:ℝ) by positivity)
  nlinarith only [m,e]
end
end ArticuloA.RealFinita
#print axioms ArticuloA.RealFinita.salida_por_deriva
#print axioms ArticuloA.RealFinita.exponente_hasta_el_corte
