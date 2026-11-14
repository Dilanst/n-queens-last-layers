import TransicionAntesDeLaPrimeraSalida
import BorradosDelParInverso
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

private theorem marcas_distintas {α} (l : List α) (nd : l.Nodup) (ij : α×α) (hi : ij∈E2.pairs l) :
    ij.1≠ij.2 := by
  induction l with
  | nil => simp [E2.pairs] at hi
  | cons x xs ih =>
    rcases List.mem_append.mp hi with a|b
    · obtain ⟨t,ht,rfl⟩:=List.mem_map.mp a
      change x≠t
      exact fun eq => (List.nodup_cons.mp nd).1 (eq.symm ▸ ht)
    · exact ih (List.nodup_cons.mp nd).2 b

theorem exceso_de_borrados_en_la_region {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (nn : 0<n) (l : List Vertex) (nd : l.Nodup) (hit : Choice n→Vertex→Prop)
    (sub : ∀ a j,hit a j → consumeVertex a j.1 j.2) :
    (n:ℝ≥0)^2*meanN masas (choices masas X w (·⁻¹)) (fun a => deathsOn l (hit a)-1)≤
      ((E2.pairs l).length:ℝ≥0)*(A.mr/A.l+4*(A.mv/A.l^4)) := by
  classical
  let cap:=A.mr/A.l+4*(A.mv/A.l^4)
  let row:=choices masas X w (·⁻¹)
  have np : 0<(n:ℝ≥0)^2 := pow_pos (by exact_mod_cast nn) 2
  have each (ij : Vertex×Vertex) (mem : ij∈E2.pairs l) :
      masas.le (meanN masas row (fun a => Repair.indicator (hit a ij.1 ∧ hit a ij.2))) (cap/(n:ℝ≥0)^2) := by
    have d:=dos_lineas_en_una_eleccion A ij.1 ij.2 (marcas_distintas l nd ij mem)
    have cmp:=mean_le masas row (fun a => Repair.indicator (hit a ij.1 ∧ hit a ij.2))
      (fun a => Repair.indicator (consumeVertex a ij.1.1 ij.1.2 ∧ consumeVertex a ij.2.1 ij.2.2)) (by
        intro a _
        by_cases h : hit a.2 ij.1 ∧ hit a.2 ij.2
        · simp [Repair.indicator,h,sub _ _ h.1,sub _ _ h.2]
        · simp [Repair.indicator,h])
    apply (le_div_iff₀ np).mpr
    rw [mul_comm]; exact (mul_le_mul_left' cmp _).trans d
  have sum:=exchange_bound masas row l hit (cap/(n:ℝ≥0)^2) each
  rw [times_m,ns_real] at sum
  apply le_trans (mul_le_mul_left' sum ((n:ℝ≥0)^2))
  change (n:ℝ≥0)^2*(_*(cap/(n:ℝ≥0)^2))≤_*cap
  exact le_of_eq (by field_simp)
  
theorem solapamiento_de_las_diez_lineas {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (e f : Cell n) (compatiblePair : compatible e f) (hit : Choice n→Vertex→Prop)
    (sub : ∀ a j,hit a j → consumeVertex a j.1 j.2) :
    (n:ℝ≥0)^2*meanN masas (choices masas X (coloresDelPerfil n h p) (·⁻¹))
      (fun a => deathsOn (diez e f) (hit a)-1)≤45*(m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)) := by
  let A:=region_del_estado hn hh sp kp m1 zp hz z1 bal he ho X reg
  have b:=exceso_de_borrados_en_la_region A (by omega) _ (diez_distintas e f compatiblePair) hit sub
  have len : (E2.pairs (diez e f)).length =45 := rfl
  rw [len] at b
  exact b
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.solapamiento_de_las_diez_lineas
