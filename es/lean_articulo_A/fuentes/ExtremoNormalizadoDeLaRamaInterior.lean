import LimiteDeLaRamaInteriorSinPerfilPrefijado
import NormalizacionDeLosCamposEnElExtremo
import TableroMedidoConstruidoEnElLleno
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
theorem extremo_normalizado_desde_una_sucesion {P : ℕ→TableroMedido} {p : ℕ→FactoresContinuos}
    {b : ℕ→ℝ} {x : ℕ→ℝ≥0} {κ M L : ℝ} (kp : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (lp : 0≤L)
    (eq : ∀ j,EulerFisica (P j) (p j) (x j) (b j)) (sp : ∀ j,ControlEspacial (p j) κ M L)
    (xp : ∀ j,0<x j) (half : ∀ j,(x j:ℝ)≤1/2) (zero : Tendsto (fun j=>(x j:ℝ)) atTop (𝓝 0)) :
    ∃ (P₀ : TableroMedido) (p₀ : FactoresContinuos) (b₀ : ℝ),EulerFisica P₀ p₀ 0 b₀ ∧
      ControlEspacial p₀ κ M L ∧ NormalizacionR15 p₀ ∧ Tendsto b atTop (𝓝 b₀) ∧
      ∀ i,TendstoUniformlyOn (fun j=>camposFisicos (p j) i) (camposFisicos p₀ i) atTop (rangoF i) := by
  obtain ⟨b₀,bp,bl,f,lim⟩:=limite_uniforme_de_la_rama_interior atTop kp k1 m1 lp eq sp xp half zero
  have pt i s (hs : s∈rangoF i) := (lim i).2.tendsto_at hs
  obtain ⟨sp0,pos⟩:=control_del_representante_limite sp kp.le pt
  let p₀:=factoresEnElExtremo f
  have pc i : Continuous (camposFisicos p₀ i) := representante_continuo_sobre_la_recta (fun i=>(lim i).1) pos i
  have pu i : TendstoUniformlyOn (fun j=>camposFisicos (p j) i) (camposFisicos p₀ i) atTop (rangoF i) := by
    intro u hu
    filter_upwards [(lim i).2 u hu] with j hj
    intro s hs
    rw [representante_en_su_intervalo pos i hs]
    exact hj s hs
  have lc i s (hs : s∈rangoF i) := (pu i).tendsto_at hs
  obtain ⟨P₀,e₀⟩:=tablero_medido_desde_el_limite bp kp eq sp bl zero pc lc
  exact ⟨P₀,p₀,b₀,e₀,sp0,normalizacion_de_los_campos_en_el_extremo sp lp
    (fun j=>normalizacion_R15_en_masa_interior (eq j) (xp j)) lc,bl,pu⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.extremo_normalizado_desde_una_sucesion
