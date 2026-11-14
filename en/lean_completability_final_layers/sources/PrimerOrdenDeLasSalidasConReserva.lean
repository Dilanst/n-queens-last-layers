import CandidatosDeLasLineasReservadas
import CostoSublinealDeLasMarcas
import ValorDeAbsorcionEnCoordenadasCartesianas
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

/-- Geometric part of the event E, on the squares of the paper. -/
def SalidaDeReserva {n} (m : ℕ) (D A : ℤ→Prop) (p : Placement n) : Prop :=
  Legal p ∧ pieces p+m=n ∧ (∀ e∈queens p,¬D (llaveDeLinea 2 e) ∧ ¬A (llaveDeLinea 3 e)) ∧
    ∀ z : Cell n,9*m+3≤(candidatasDeReserva p z D A).card

theorem la_salida_de_reserva_se_completa {n m} {D A : ℤ→Prop} {p : Placement n}
    (sal : SalidaDeReserva m D A p) :
    ∃ ms : Fin m→Mark n,aplicarMarcas (List.ofFn ms) p∈nivel n n := by
  obtain ⟨hp,size,libres,roots⟩:=sal
  have high (z : Cell n) : 9*m≤physicalCount p z+8 := by
    have lower:=roots z
    have upper:=candidatas_menos_cuatro hp z D A libres
    omega
  obtain ⟨ms,len,ok⟩:=completar_si_hay_nueve_por_hueco p hp size high
  subst m
  exact ⟨ms.get,by simpa using ok⟩

/-- Only the outputs of G enter this budget.
The multiplicity error is proved through the cost of the marks. -/
theorem primer_orden_desde_el_evento_de_reserva {s C d : ℝ} (dp : 0<d)
    (m : ℕ→ℕ) (O : (n : ℕ)→Finset (Placement n)) (r : ℕ→ℝ)
    (sizes : ∀ᶠ n : ℕ in atTop,(m n:ℝ)≤C*(n:ℝ)^(1-d))
    (loss : Tendsto (fun n : ℕ=>r n/(n:ℝ)) atTop (𝓝 0))
    (good : ∀ᶠ n : ℕ in atTop,(O n).Nonempty ∧
      (n:ℝ)*log n+(n:ℝ)*s-r n≤log ((O n).card:ℝ) ∧
      ∃ D A : ℤ→Prop,∀ p∈O n,SalidaDeReserva (m n) D A p) :
    exp s≤liminf (raizDelConteo (fun n=>count n n)) atTop := by
  apply raiz_desde_las_tolerancias
  apply primer_orden_de_las_salidas_completables m O r loss (costo_de_marcas_es_sublineal dp sizes)
  filter_upwards [good] with n h
  obtain ⟨ne,large,D,A,legal⟩:=h
  exact ⟨ne,large,fun p hp=>la_salida_de_reserva_se_completa (legal p hp)⟩

/-- The six pieces keep the same laws and the same physical profile. -/
def ConclusionDelArticuloA : Prop :=
  ∃ (P : ℝ→TableroMedido) (p : ℝ→FactoresContinuos) (b : ℝ→ℝ) (κ M L : ℝ),
      0<κ ∧ κ≤1 ∧ 1≤M ∧ 0≤L ∧ 0<fraccionDelPerfil b 0 ∧
      (∀ x∈Icc 0 (1/2:ℝ),EulerFisica (P x) (p x) x.toNNReal (b x)) ∧
      (∀ x∈Icc 0 (1/2:ℝ),ControlEspacial (p x) κ M L) ∧ NormalizacionR15 (p 0) ∧
      IsGreatest valoresAdmisiblesLlenos (valorCentrado (P 0)) ∧ ResultadosDeCapas p b κ

theorem articulo_desde_N3A2_14 {C d : ℝ} (dp : 0<d)
    (bound : ∀ᶠ n : ℕ in atTop, (n:ℝ)*log n+(n:ℝ)*sSup valoresCartesianosDeAbsorcion
      -C*(n:ℝ)^(1-d)≤log ((conjuntosLegales n n).card:ℝ)) : ConclusionDelArticuloA := by
  simp only [conteo_de_conjuntos_es_el_del_articulo,los_dos_dominios_de_valores_finitos_coinciden] at bound
  exact articulo_A_desde_el_primer_orden_variacional (raiz_desde_las_tolerancias (tolerancias_desde_absorcion dp bound))

theorem articulo_desde_las_salidas_de_G {C d : ℝ} (dp : 0<d) (m : ℕ→ℕ)
    (O : (n : ℕ)→Finset (Placement n)) (r : ℕ→ℝ)
    (sizes : ∀ᶠ n : ℕ in atTop,(m n:ℝ)≤C*(n:ℝ)^(1-d))
    (loss : Tendsto (fun n : ℕ=>r n/(n:ℝ)) atTop (𝓝 0))
    (good : ∀ᶠ n : ℕ in atTop,(O n).Nonempty ∧
      (n:ℝ)*log n+(n:ℝ)*sSup valoresCartesianosDeAbsorcion-r n≤log ((O n).card:ℝ) ∧
      ∃ D A : ℤ→Prop,∀ p∈O n,SalidaDeReserva (m n) D A p) : ConclusionDelArticuloA := by
  apply articulo_A_desde_el_primer_orden_variacional
  rw [←los_dos_dominios_de_valores_finitos_coinciden]
  exact primer_orden_desde_el_evento_de_reserva dp m O r sizes loss good

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.la_salida_de_reserva_se_completa
#print axioms ArticuloA.Historias.primer_orden_desde_el_evento_de_reserva
#print axioms ArticuloA.Historias.articulo_desde_N3A2_14
#print axioms ArticuloA.Historias.articulo_desde_las_salidas_de_G
