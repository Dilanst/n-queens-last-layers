import ConstanteVariacionalDeLaEntradaDeConteo
import LeyDeImagenDesdePruebasBorel
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- Here we work in (column,row), with D=y−x. -/
def lineaCartesiana (i : Fin 4) (z : ℝ×ℝ) := coord i z.swap

/-- The law of the fibers is expressed through bounded Borel tests.
Values with finite real entropy suffice for the supremum of the functional. -/
def valoresCartesianosEnMasa (d : ℝ) : Set ℝ := {s | ∃ ν : ℝ×ℝ→ℝ≥0, ∃ m : Fin 4→ℝ→ℝ≥0,
  Measurable ν ∧ (∀ i,Measurable (m i)) ∧ Integrable (fun z=>(ν z:ℝ)) cuadrado ∧
  (∀ i, Integrable (fun t=>(m i t:ℝ)) (marginalRef i)) ∧
  (∀ i,∀ᵐ t ∂marginalRef i,(m i t:ℝ)≤1) ∧ masaDensidad ν=d ∧
  (∀ i,∀ w : ℝ→ℝ,Measurable w → (∀ t,‖w t‖≤1) →
    (∫ z,(ν z:ℝ)*w (lineaCartesiana i z) ∂cuadrado)=∫ t,(m i t:ℝ)*w t ∂marginalRef i) ∧
  Integrable (fun z=>xlogx (ν z)) cuadrado ∧
  (∀ i,Integrable (fun t=>xlogx (1-(m i t:ℝ))) (marginalRef i)) ∧
  s=valorEntropico ν (fun i t=>1-(m i t:ℝ))}

abbrev valoresCartesianosDeAbsorcion := valoresCartesianosEnMasa 1

def valoresMedidosEnMasa (d : ℝ) : Set ℝ := {s | ∃ P : TableroMedido, P.rho=d ∧
  Integrable (fun z=>xlogx (P.ν z)) cuadrado ∧ (∀ i,Integrable (fun t=>xlogx (P.u i t)) (marginalRef i)) ∧ s=P.s}

theorem integral_en_coordenadas_del_manuscrito (f : ℝ×ℝ→ℝ) :
    (∫ z,f z.swap ∂cuadrado)=∫ z,f z ∂cuadrado := integral_prod_swap f

private theorem masa_swap (ν : ℝ×ℝ→ℝ≥0) :
    masaDensidad (fun z : ℝ×ℝ=>ν z.swap)=masaDensidad ν :=
  integral_en_coordenadas_del_manuscrito (fun z=>(ν z:ℝ))

private theorem valor_swap (ν : ℝ×ℝ→ℝ≥0) (u : Fin 4→ℝ→ℝ) :
    valorEntropico (fun z : ℝ×ℝ=>ν z.swap) u=valorEntropico ν u := by
  unfold valorEntropico
  rw [masa_swap,integral_en_coordenadas_del_manuscrito (fun z=>xlogx (ν z))]

theorem conjuntos_de_valores_en_cada_masa (d : ℝ) :
    valoresCartesianosEnMasa d=valoresMedidosEnMasa d := by
  ext s
  constructor
  · rintro ⟨ν,m,nm,mm,ni,mi,cap,mass,adj,entr,lines,value⟩
    let Q : TableroMedido := {
      ν:=fun z=>ν z.swap, m:=m, masaFinita:=ni.swap, admisible:=cap
      ley:=ley_marginal_desde_pruebas_borel (nm.comp measurable_swap) mm ni.swap mi
        (fun i w wm wb=>by
          have eq:=integral_en_coordenadas_del_manuscrito (fun z=>(ν z:ℝ)*w (lineaCartesiana i z))
          exact eq.trans (adj i w wm wb)) }
    refine ⟨Q,(masa_swap _).trans mass,entr.swap,lines,?_⟩
    exact value.trans (valor_swap ν _).symm
  · rintro ⟨Q,mass,entr,lines,value⟩
    refine ⟨fun z=>Q.ν z.swap,Q.m,Q.ley.densidad.comp measurable_swap,Q.ley.densidadLinea,
      Q.masaFinita.swap,Q.m_integrable,Q.admisible,(masa_swap _).trans mass,?_,entr.swap,lines,?_⟩
    · intro i w wm _
      exact (integral_en_coordenadas_del_manuscrito (fun z=>(Q.ν z:ℝ)*w (coord i z))).trans
        (adjuncion Q.ley i w wm)
    · exact value.trans (valor_swap Q.ν _).symm

theorem los_dos_dominios_de_valores_finitos_coinciden :
    valoresCartesianosDeAbsorcion=valoresAdmisiblesLlenos := conjuntos_de_valores_en_cada_masa 1
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.conjuntos_de_valores_en_cada_masa
#print axioms ArticuloA.Historias.integral_en_coordenadas_del_manuscrito
#print axioms ArticuloA.Historias.los_dos_dominios_de_valores_finitos_coinciden
