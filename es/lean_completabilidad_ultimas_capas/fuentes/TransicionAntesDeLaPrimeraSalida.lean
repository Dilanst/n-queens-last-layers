import RiesgosDeUnaYDosLineas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

/-- Conditional on the four observed errors, with the actual real/virtual kernel.
All constants on the right depend only on the spatial bounds and fixed cutoff. -/
theorem tasas_de_la_transicion_fisica {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (X : State n) (reg : Seguimiento h p X z E) (j j' : Vertex) (dist : j≠j') (live : activeLine X j) :
    let w:=coloresDelPerfil n h p
    let l:=piso κ ζ
    let clk:=relojIni n*z
    within masas ((n:ℝ≥0)^2*(realRate masas X w (·⁻¹) j+virtRate masas X w (·⁻¹) j))
        ((n:ℝ≥0)*clk⁻¹) (constanteUna l (techo m κ ζ) C*(E+1)) ∧
    (n:ℝ≥0)^2*meanN masas (choices masas X w (·⁻¹))
      (fun i => Repair.indicator (consumeVertex i j.1 j.2 ∧ consumeVertex i j'.1 j'.2))≤m^4/l+4*(m^4/l^4) := by
  intro w l clk
  let A:=region_del_estado hn hh sp kp m1 zp hz z1 bal he ho X reg
  have pos : 0<n := by omega
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast pos.ne'
  have cancel (v : ℝ≥0) : (n:ℝ≥0)*(v/n)≤v := le_of_eq (by field_simp)
  exact ⟨riesgo_de_una_linea A E C (cancel E) (cancel (2*C)) (cancel C) j live (⟨0,pos⟩,⟨0,pos⟩),
    dos_lineas_en_una_eleccion A j j' dist⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.tasas_de_la_transicion_fisica
