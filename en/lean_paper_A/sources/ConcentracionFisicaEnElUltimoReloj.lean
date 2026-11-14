import AbsorbedoresSimultaneosAntesDelCorte
import VariacionFisicaEnTodaHistoria
import BlancoAlAgotarElReloj
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def blancoFinalDeMalla {n} (h : ℕ) (p : FactoresContinuos) (z : Cell n) :=
  blancoDeLaRaiz 1 z (cargaDeDestino h p z) (probDeLaCasilla h p)

/-- A deterministic cut of the padded clock. The remaining number of attempted
steps bounds the physical changes even on paths that eventually fail. -/
theorem control_final_con_corte_fijo {n h T : ℕ} (p : FactoresContinuos) (γ M : ℝ≥0) (tp : T≤2*n-1)
    (np : 0<2*n-1) (load : ∀ (z e : Cell n) (j : Fin 4),cargaDeDestino h p z e j≤1)
    (cap : ∀ e : Cell n,(n:ℝ≥0)*probDeLaCasilla h p e≤M) :
    let N:=2*n-1
    let S:=kernel masas (coloresDelPerfil n h p) (·⁻¹)
    let y:ℝ≥0:=(T:ℝ≥0)/N
    let b:=fun z (j : ℕ) => blancoDeLaRaiz ((j:ℝ≥0)/(N:ℝ≥0)) z (cargaDeDestino h p z) (probDeLaCasilla h p)
    let X:=fun l j => estadoEn (initial n h) l j
    avg masas (rutas S 0 N (initial n h)) (mark masas (fun l => ∃ z,
      (γ:ℝ)*n+4*(↑(N-T):ℝ)+(1-(y:ℝ))*M*n ≤ |(physicalCount (X l N).physical z:ℝ)-(blancoFinalDeMalla h p z:ℝ)|)) ≤
    avg masas (rutas S 0 T (initial n h)) (mark masas (fun l => ∃ z,∃ j≤T,
      (γ:ℝ)*n≤|(physicalCount (X l j).physical z:ℝ)-(b z j:ℝ)|)) := by
  intro N S y b X
  let good:=fun l => ∃ z,∃ j≤T,(γ:ℝ)*n≤|(physicalCount (X l j).physical z:ℝ)-(b z j:ℝ)|
  have norm : ∀ t x,total masas (S t x)=1 := kernel_total masas _ _ (fun _ h => inv_mul_cancel₀ h) (by
    intro i j ij
    change masas.add (ns masas i) (ns masas j)≠masas.zero
    rw [ns_real,ns_real]; change (i:ℝ≥0)+j≠0; rw [←Nat.cast_add]; exact_mod_cast ij)
  rw [←probabilidad_del_prefijo S norm (mark masas good) (initial n h) 0 T N tp]
  apply misma_masa_en_el_soporte
  rintro i mi nz ⟨z,bad⟩
  have variation:=oscilacion_en_la_historia (coloresDelPerfil n h p) i mi nz T N tp le_rfl z
  have hy : y≤1 := (div_le_one (by exact_mod_cast np)).mpr (by exact_mod_cast tp)
  have target:=blanco_hasta_uno z y hy _ _ (load z) M cap
  change |(b z T:ℝ)-(blancoFinalDeMalla h p z:ℝ)|≤_ at target
  change |(physicalCount (X i.2 N).physical z:ℝ)-physicalCount (X i.2 T).physical z|≤_ at variation
  have take : X (i.2.take T) T=X i.2 T := by simp only [X,estadoEn,List.take_take,min_self]
  refine ⟨z,T,le_rfl,?_⟩
  rw [take]
  have a:=abs_sub_le (physicalCount (X i.2 N).physical z:ℝ) (physicalCount (X i.2 T).physical z)
    (blancoFinalDeMalla h p z:ℝ)
  have d:=abs_sub_le (physicalCount (X i.2 T).physical z:ℝ) (b z T:ℝ) (blancoFinalDeMalla h p z:ℝ)
  linarith only [a,d,bad,target,variation]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_final_con_corte_fijo
