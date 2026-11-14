import CuatroMasasDesdeElTablero
import ModuloIntegralDeLaDensidad
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
private theorem umbral_de_raiz {C H η : ℝ} (cn : 0≤C) (hn : 0≤H) (ep : 0<η) :
    ∃ d : ℝ,0<d ∧ ∀ Δ x : ℝ,Δ^2≤C*x → 0≤x → x<d → H*Δ≤η := by
  let u:=η/(H+1)
  have up : 0<u := div_pos ep (by linarith)
  have ident : u*(H+1)=η := div_mul_cancel₀ _ (by linarith)
  refine ⟨u^2/(C+1),div_pos (pow_pos up 2) (by linarith),?_⟩
  intro Δ x bd xn xs
  have sx:=(lt_div_iff₀ (by linarith : 0<C+1)).mp xs
  have dlt : Δ≤u := le_of_sq_le_sq (by nlinarith only [bd,xn,sx]) up.le
  exact (mul_le_mul_of_nonneg_left dlt hn).trans (by linarith only [ident,up])

theorem criterio_R15_entre_parametros {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    {η : ℝ} (ep : 0<η) : ∃ d : ℝ,0<d ∧ ∀ {P Q p q x y b c},
    EulerFisica P p x b → EulerFisica Q q y c → ControlEspacial p κ M L → ControlEspacial q κ M L →
    NormalizacionR15 p → NormalizacionR15 q → (x:ℝ)≤1/2 → (y:ℝ)≤1/2 → |(y:ℝ)-x|<d →
    |b-c|≤η ∧ (∑ i,masaExterior (fun j s=>|camposFisicos p j s-camposFisicos q j s|) i)≤η := by
  let m:=(1/2:ℝ)/M^4
  let H:=constanteDeLasVacancias κ
  let C:=constanteDiferenciaDensa κ M
  have Mpos:=zero_lt_one.trans_le m1
  have mp : 0<m := div_pos (by norm_num) (pow_pos Mpos 4)
  have kn : 0≤1-κ := sub_nonneg.mpr k1
  have hp : 0≤H := by dsimp [H,constanteDeLasVacancias]; positivity
  have cp : 0≤C := by dsimp [C,constanteDiferenciaDensa]; positivity
  obtain ⟨d,dp,mod⟩:=umbral_de_raiz cp (hp.trans (le_max_left H (4*H/m+2))) ep
  refine ⟨d,dp,?_⟩
  intro P Q p q x y b c ex ey sx sy gx gy hx hy small
  have dens:=modulo_L1_de_la_densidad_fisica ex ey sx sy kp m1 lp hx hy
  have low:=banda_del_normalizador ex sx kp m1 hx
  obtain ⟨db,dm⟩:=cuatro_masas_y_el_normalizador ex ey gx gy sx sy kp k1 lp mp low.1
  have nn : 0≤distanciaTableros P Q := integral_nonneg (fun _=>abs_nonneg _)
  have final:=mod _ _ dens (abs_nonneg _) small
  exact ⟨db.trans ((mul_le_mul_of_nonneg_right (le_max_left H (4*H/m+2)) nn).trans final),
    dm.trans ((mul_le_mul_of_nonneg_right (le_max_right H (4*H/m+2)) nn).trans final)⟩

theorem control_R15_hasta_el_lleno {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (g0 : NormalizacionR15 (p 0)) :
    ∀ η : ℝ,0<η → ∃ d : ℝ,0<d ∧ ∀ x∈Icc 0 (1/2:ℝ),x<d →
      |b 0-b x|≤η ∧ (∑ g,masaExterior (fun j y=>|camposFisicos (p x) j y-camposFisicos (p 0) j y|) g)≤η := by
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  intro η ep
  obtain ⟨d,dp,step⟩:=criterio_R15_entre_parametros kp k1 m1 lp ep
  refine ⟨d,dp,?_⟩
  intro x hx xd
  have r : (x.toNNReal:ℝ)=x := Real.coe_toNNReal x hx.1
  have half : (x.toNNReal:ℝ)≤1/2 := r.le.trans hx.2
  have gx : NormalizacionR15 (p x) := by
    rcases eq_or_lt_of_le hx.1 with xx|xx
    · rw [←xx]; exact g0
    · exact normalizacion_R15_en_masa_interior (eq x hx) (Real.toNNReal_pos.mpr xx)
  obtain ⟨db,dm⟩:= step (eq x hx) (eq 0 z) (sp x hx) (sp 0 z) gx g0 half (by norm_num)
    (by simpa [r,abs_of_nonneg hx.1] using xd)
  exact ⟨(abs_sub_comm _ _).le.trans db,dm⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_R15_hasta_el_lleno
#print axioms ArticuloA.Historias.criterio_R15_entre_parametros
