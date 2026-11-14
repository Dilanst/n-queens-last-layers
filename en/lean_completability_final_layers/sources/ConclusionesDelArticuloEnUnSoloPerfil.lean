import ContinuidadAbsolutaDelPerfilCentrado
import CotaPositivaDeLasUltimasCapas
import RamaCompletaConElMismoExtremo
import ReparacionTipicaEnCadaCruce
import LeyEspacialDeLasUltimasCapas
import ConstanteDelConteoSinPeso
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

structure ResultadosDeCapas (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ : ℝ) : Prop where
  entropia : ∀ K : ℕ,∃ d : ℕ→ℝ,Tendsto (fun n : ℕ=>d n/(n:ℝ)) atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop,∀ h≤K,Tres n h (coloresDelPerfil n h (p ((h:ℝ)/n))) (d n)
  positiva : ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,c≤fracReal n 1 ∧ c≤fracReal n 2
  pisoExplicito : ∀ h : ℕ,h=1 ∨ h=2 → ((κ/2)^4/16)/2≤liminf (fun n=>fracReal n h) atTop
  uniformeFijo : ∀ K : ℕ,∀ ε>0,∀ᶠ n : ℕ in atTop,∀ h∈Icc 1 K,|fracReal n h-fraccionDelPerfil b 0|<ε
  limite : ∀ h : ℕ,0<h → Tendsto (fun n=>fracReal n h) atTop (𝓝 (fraccionDelPerfil b 0))
  cociente : ∀ K,Tendsto (fun n=>conteoEscalado n K) atTop (𝓝 (1/(fraccionDelPerfil b 0)^K))
  residual : ∀ K : ℕ,∀ s∈Icc (0:ℝ) 1,Tendsto (fun n : ℕ=>∑ j∈Finset.range K,
    Real.log (fracReal n (j+1)/fraccionDelPerfil b (((j:ℝ)+1-s)/n))) atTop (𝓝 0)
  porCruce : ∀ h : ℕ,0<h → ∀ η>0,Tendsto (fun n=>probCruceMalo n h (aDelLleno p b) η) atTop (𝓝 0)
  reparacion : ∃ t : ℝ,0<t ∧ ∀ h : ℕ,0<h → Tendsto (fun n=>probabilidadDeCruceEscaso n h t) atTop (𝓝 0)
  espacial : ∀ h : ℕ,0<h → ∀ t : ℝ×ℝ→ℝ,ContinuousOn t cuadradoCerrado →
    Tendsto (fun n : ℕ=>promedioNivel n (n-h) (fun Q=>mediaCruces Q h (valorEnCentro t)))
      atTop (𝓝 (integralDeLosHuecos (p 0) t))
  inversa : ∀ h : ℕ,0<h → concentracionInversaFisica p b h
  sinPeso : ∀ h : ℕ,0<h → (∀ ε>0,Tendsto (fun n=>desviacion n (n-h+1) (Iobs n h (fun _=>1))
    (integralTablero (psiDiagonal (p 0))) ε) atTop (𝓝 0)) ∧
    Tendsto (fun n=>mediaD n h (fun _=>1)) atTop (𝓝 (integralTablero (psiDiagonal (p 0))/b 0))

/-- The full profile is chosen before asking for the single lower counting bound. -/
theorem resultados_del_articulo_en_un_solo_perfil :
    ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ M L : ℝ),
      0<κ ∧ κ≤1 ∧ 1≤M ∧ 0≤L ∧ 0<fraccionDelPerfil b 0 ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)) ∧
      (∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) ∧
      NormalizacionR15 (p 0) ∧ admisibleParaConteo (P 0) ∧
      (AdmisibleCentrada (leyCentrada (P 0)) ∧ leyCentrada (P 0) ≪ (volume : Measure (ℝ×ℝ))) ∧ valorCentrado (P 0)=(P 0).s ∧
      (Real.exp (valorCentrado (P 0))≤liminf (raizDelConteo (fun n=>count n n)) atTop →
        ResultadosDeCapas p b κ) := by
  obtain ⟨P,p,b,κ,M,L,kp,k1,m1,lp,g,eq,sp⟩:=existe_rama_normalizada_del_articulo
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ):=⟨le_rfl,by norm_num⟩
  have full : EulerFisica (P 0) (p 0) 0 (b 0):=by simpa using eq 0 z
  have fp : 0<fraccionDelPerfil b 0 := by simpa [fraccionDelPerfil] using (one_div_pos.mpr full.coef)
  refine ⟨P,p,b,κ,M,L,kp,k1,m1,lp,fp,eq,sp,g,perfil_lleno_admisible full,ley_llena_admisible_y_absolutamente_continua full,
    normalizacion_de_simkin full (sp 0 z) kp lp,?_⟩
  intro bound
  obtain ⟨rama,cont,first⟩:=premisas_del_articulo_desde_euler_normalizada kp k1 m1 lp eq sp g
    (fun _=>testigo_del_primer_orden_global le_rfl bound)
  have scal := conclusiones_de_capas_fijas rama cont first
  have uniform (K : ℕ) (ε : ℝ) (ep : 0<ε) :
      ∀ᶠ n : ℕ in atTop,∀ h∈Icc 1 K,|fracReal n h-fraccionDelPerfil b 0|<ε := by
    apply (eventually_all_finite (Set.finite_Icc 1 K)).2
    intro h hn
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ((scal h).2.1 h (by have := hn.1; omega) le_rfl) ε ep
  have piso:=dos_ultimas_capas_del_articulo rama (euler_puntual_de_la_rama rama)
    (fun _=>(conteo_equivalente_al_primer_orden _).mpr first)
  exact ⟨fun K=>L1_de_la_rama_y_el_conteo rama K (fun _=>(conteo_equivalente_al_primer_orden _).mpr first),
    (scal 1).1,piso.1,uniform,fun h hh=>(scal h).2.1 h hh le_rfl,fun K=>(scal K).2.2.1,fun K=>(scal K).2.2.2,
    fun h hh=>(directa_del_articulo rama (euler_puntual_de_la_rama rama) cont first h hh).1,
    reparacion_tipica_en_cada_cruce rama cont first,ley_espacial_media_de_los_cruces rama cont first,
    inversa_con_el_peso_del_articulo rama cont first,ley_del_conteo_sin_peso rama cont first⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.resultados_del_articulo_en_un_solo_perfil
