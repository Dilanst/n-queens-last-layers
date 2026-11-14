import LasDiezIntensidadesDelGenerador
import ErrorRealDeLosNacimientosInversos
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def intensidadIdeal {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (u : Vertex) (b : Bool) : ℝ≥0 :=
  (if b then A.time⁻¹ else A.time⁻¹*A.p u)/n

def errorDeLinea {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (u : Vertex) (b : Bool) : ℝ≥0 :=
  ⟨|(tasaDeMarca X w u b:ℝ)-(intensidadIdeal A u b:ℝ)|,abs_nonneg _⟩

theorem error_de_la_tasa_en_linea_activa {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (hn : 0<n) (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (u : Vertex) (on : activeLine X u) (e : Cell n) (b : Bool) :
    (n:ℝ≥0)^2*errorDeLinea A u b≤constanteUna A.l A.M C*(E+1) := by
  let target:=if b then A.time⁻¹ else A.time⁻¹*A.p u
  have est:=A.estimates (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _)) u on e
  simp only [ns_real] at est
  have near : within masas ((n:ℝ≥0)*tasaDeMarca X w u b) target A.combined := by
    cases b
    · apply grow masas _ (show A.budget≤A.combined from
        (le_add_of_nonneg_right (zero_le _)).trans (le_add_of_nonneg_right (zero_le _)))
      simpa [tasaDeMarca,target] using est.1
    · exact est.2.2.1
  have delta:=(presupuesto_absoluto _ _ _).mp near
  have np : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have eq : (n:ℝ)*((tasaDeMarca X w u b:ℝ)-((target/(n:ℝ≥0):ℝ≥0):ℝ)) =
      (↑((n:ℝ≥0)*tasaDeMarca X w u b):ℝ)-(target:ℝ) := by
    push_cast; field_simp; ring
  rw [←eq,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)] at delta
  have scaled:=mul_le_mul_of_nonneg_left delta (Nat.cast_nonneg n : (0:ℝ)≤n)
  apply le_trans _ (presupuesto_escalado A E C he ho hb)
  change (↑((n:ℝ≥0)^2*errorDeLinea A u b):ℝ)≤(↑((n:ℝ≥0)*A.combined):ℝ)
  simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast,pow_two,mul_assoc,errorDeLinea,
    intensidadIdeal,target] using scaled

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.error_de_la_tasa_en_linea_activa
