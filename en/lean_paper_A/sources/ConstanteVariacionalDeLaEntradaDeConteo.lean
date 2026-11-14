import MaximoDelValorEnLaMasaLlena
import ConclusionesDelArticuloEnUnSoloPerfil
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- The entropy costs are defined as finite integrals. -/
def valoresAdmisiblesLlenos : Set ℝ :=
  {v | ∃ Q : TableroMedido,Q.rho=1 ∧ Integrable (fun z=>xlogx (Q.ν z)) cuadrado ∧
    (∀ i,Integrable (fun t=>xlogx (Q.u i t)) (marginalRef i)) ∧ v=Q.s}

theorem extremo_alcanza_el_supremo {P : ℝ→TableroMedido} {p : ℝ→FactoresContinuos} {b : ℝ→ℝ}
    {κ M L : ℝ} (kp : 0<κ) (mm : 1≤M) (lp : 0≤L)
    (eq : ∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x))
    (sp : ∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) (g : NormalizacionR15 (p 0)) :
    IsGreatest valoresAdmisiblesLlenos (valorCentrado (P 0)) := by
  have z : (0:ℝ)∈Icc 0 (1/2:ℝ):=⟨le_rfl,by norm_num⟩
  have e : EulerFisica (P 0) (p 0) 0 (b 0):=by simpa using eq 0 z
  rw [normalizacion_de_simkin e (sp 0 z) kp lp]
  obtain ⟨qi,ui⟩:=entropias_del_optimo_integrables e (sp 0 z) kp lp
  refine ⟨⟨P 0,by simpa using e.masa,qi,ui,rfl⟩,?_⟩
  rintro y ⟨Q,mass,intQ,intU,rfl⟩
  exact el_perfil_lleno_domina_a_cada_competidor kp mm lp eq sp g Q mass intQ intU

theorem articulo_A_desde_el_primer_orden_variacional
    (primerOrden : exp (sSup valoresAdmisiblesLlenos)≤liminf (raizDelConteo (fun n=>count n n)) atTop) :
    ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ M L : ℝ),
      0<κ ∧ κ≤1 ∧ 1≤M ∧ 0≤L ∧ 0<fraccionDelPerfil b 0 ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)) ∧
      (∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) ∧ NormalizacionR15 (p 0) ∧
      IsGreatest valoresAdmisiblesLlenos (valorCentrado (P 0)) ∧ ResultadosDeCapas p b κ := by
  obtain ⟨P,p,b,κ,M,L,kp,k1,mm,lp,fp,eq,sp,g,_,_,_,applyCount⟩:=resultados_del_articulo_en_un_solo_perfil
  have mx:=extremo_alcanza_el_supremo kp mm lp eq sp g
  exact ⟨P,p,b,κ,M,L,kp,k1,mm,lp,fp,eq,sp,g,mx,applyCount (by rwa [←mx.csSup_eq])⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.extremo_alcanza_el_supremo
#print axioms ArticuloA.Historias.articulo_A_desde_el_primer_orden_variacional
