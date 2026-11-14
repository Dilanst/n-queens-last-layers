import ContinuidadAlLlenoDesdeLasMasasL1
import PrimerOrdenConVecindadesVariables
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Limites Perfil
open scoped Topology
theorem entradas_para_las_capas_desde_las_masas {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos}
    {b : ℝ→ℝ} {κ M L : ℝ} (hk : 0<κ) (k1 : κ≤1) (m1 : 1≤M) (hL : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L)
    (mass : ∀ η : ℝ,0<η → ∃ d : ℝ,0<d ∧ ∀ x∈Icc 0 (1/2:ℝ),x<d →
      |b 0-b x|≤η ∧ (∑ g,masaExterior (fun j y=>|camposFisicos (p x) j y-camposFisicos (p 0) j y|) g)≤η)
    (locales : admisibleParaConteo (P 0) → ∀ η : ℝ,0<η → ∃ S : (n : ℕ) → Finset (Placement n),
      (∀ n,S n⊆nivel n n) ∧ Real.exp (valorCentrado (P 0)-η)≤liminf (raizDelConteo (fun n=>(S n).card)) atTop) :
    RamaDensa P p b κ M L (1/κ^4) ∧ ContinuidadEnElLleno p b ∧ CotaDePrimerOrden (valorCentrado (P 0)) := by
  have hm : 0≤M := zero_le_one.trans m1
  have cap x (hx : x∈Icc 0 (1/2:ℝ)) (g : Fin 4) (t : ℝ) (ht : t∈rangoF g) : |camposFisicos (p x) g t|≤M := by
    unfold camposFisicos
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have s:=sp x hx
    fin_cases g; exacts [s.Rmax _ ht,s.Cmax _ ht,s.Dmax _ ht,s.Amax _ ht]
  have ae x (hx : x∈Icc 0 (1/2:ℝ)) (i : Fin 4) : ∀ᵐ t ∂marginalRef i,
      b x*integralFisica (p x) i t=1-holguraLinea (p x) x.toNNReal i t := by
    filter_upwards [linea_en_dominio i] with t ht
    have e:=eq x hx
    have s:=sp x hx
    fin_cases i
    · exact integral_euler_en_rectas e s hL 0 (by decide) t ht
    · exact integral_euler_en_rectas e s hL 1 (by decide) t ht
    · exact euler_oblicua_puntual e s hL false t ht
    · exact euler_oblicua_puntual e s hL true t ht
  have cont:=continuidad_en_el_lleno_desde_L1 p b hm (show 0≤1/κ^4 by positivity)
    (fun x hx g=>continua_de_cota hL (regular_familia (sp x hx) g).oscilacion) cap
    (fun x hx=>(abs_of_pos (eq x hx).coef).symm ▸ techo_desde_la_masa (eq x hx) (sp x hx) hk) ae mass
  have full : EulerFisica (P 0) (p 0) 0 (b 0) := by simpa using eq 0 ⟨le_rfl,by norm_num⟩
  exact ⟨construir_rama_desde_la_euler_medida hk k1 m1 hL eq sp cont,cont,
    primer_orden_de_euler_con_tolerancias full locales⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entradas_para_las_capas_desde_las_masas
