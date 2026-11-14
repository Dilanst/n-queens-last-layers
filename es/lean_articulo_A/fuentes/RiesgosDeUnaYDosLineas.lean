import RegionFisicaDelProcesoE2
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
private theorem reci (a : ℝ≥0) (h : a≠masas.zero) : masas.mul a⁻¹ a=masas.one := inv_mul_cancel₀ h
private theorem orden (a : ℝ≥0) (h : masas.le a masas.zero) : a=masas.zero := le_antisymm h (zero_le _)

theorem dos_lineas_en_una_eleccion {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (j j' : Vertex) (dist : j≠j') :
    (n:ℝ≥0)^2*meanN masas (choices masas X w (·⁻¹))
      (fun i => Repair.indicator (consumeVertex i j.1 j.2 ∧ consumeVertex i j'.1 j'.2))≤A.mr/A.l+4*(A.mv/A.l^4) := by
  obtain ⟨lr,lv,rr,vv⟩:=A.raw_floors reci orden
  have raw (e : Cell n) (_ : E2.available X (lines e)) : masas.le (weights masas w.real (lines e)) (A.common*A.mr) := by
    rw [A.wt]; exact mul_le_mul_left' (A.weightMax e) _
  let atom:=fromWeights masas X w (·⁻¹) rr vv (A.common*A.mr) A.mv raw A.tupleMax
  have bound:=pair_mass masas X w (·⁻¹) rr vv atom.realCap atom.virtualCap atom.capR atom.capV
    j j' dist _ (fun _ h => h)
  have l4 : masas.four (fun _ => A.l)≠masas.zero := by
    change (A.l*A.l)*(A.l*A.l)≠0; exact mul_ne_zero (mul_ne_zero A.floorPos A.floorPos) (mul_ne_zero A.floorPos A.floorPos)
  have top:=pair_from_margins masas X w (·⁻¹) reci rr vv A.running A.l A.common A.mr A.mv A.floorPos l4
    lr lv raw A.tupleMax
  change masas.le _ atom.pairCap at bound
  change masas.le (masas.times (n*n) atom.pairCap) _ at top
  simp only [times_m,ns_real,Nat.cast_mul] at top
  have f : masas.four (fun _ => A.l)=A.l^4 := by change (A.l*A.l)*(A.l*A.l)=_; ring
  rw [f] at top
  change (n:ℝ≥0)*n*atom.pairCap≤A.l⁻¹*A.mr+(4:ℝ≥0)*((A.l^4)⁻¹*A.mv) at top
  simpa only [pow_two,div_eq_mul_inv,mul_comm] using (mul_le_mul_left' bound ((n:ℝ≥0)*n)).trans top

def constanteUna (l m C : ℝ≥0) := (l*l)⁻¹*(2*m+m^2)*(2+2*C)+l⁻¹*C
theorem presupuesto_escalado {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (E C : ℝ≥0)
    (he : (n:ℝ≥0)*A.eps≤E) (ho : (n:ℝ≥0)*A.off≤2*C) (hb : (n:ℝ≥0)*A.bal≤C) :
    (n:ℝ≥0)*A.combined ≤ constanteUna A.l A.M C*(E+1) := by
  have lo : 0<A.l := lt_of_le_of_ne bot_le (Ne.symm A.floorPos)
  have it : A.time⁻¹≤A.l⁻¹ := inv_anti₀ lo A.low
  let V := (A.l*A.l)⁻¹*(2*A.M+A.M^2)
  have eq : A.combined=V*A.eps+V*(A.eps+A.off)+A.time⁻¹*A.bal := by
    have form (a x d : ℝ≥0) : cost masas a x d=a*(2*x+x^2)*d := by
      change a*((x*d+x*d)+x*(x*d))=_; ring
    change cost masas (A.l*A.l)⁻¹ A.M A.eps+cost masas (A.l*A.l)⁻¹ A.M (A.eps+A.off)+A.time⁻¹*A.bal=_
    rw [form,form]
  rw [eq]
  calc _ = V*((n:ℝ≥0)*A.eps)+V*((n:ℝ≥0)*A.eps+n*A.off)+A.time⁻¹*(n*A.bal) := by ring
       _ ≤ V*E+V*(E+2*C)+A.l⁻¹*C := add_le_add
         (add_le_add (mul_le_mul_left' he _) (mul_le_mul_left' (add_le_add he ho) _))
         (mul_le_mul it hb (zero_le _) (zero_le _))
       _ ≤ (V*E+V*(E+2*C)+A.l⁻¹*C)+(V*(2+2*C*E)+A.l⁻¹*C*E) := le_add_of_nonneg_right (zero_le _)
       _ = _ := by unfold constanteUna; dsimp only [V]; ring

theorem riesgo_de_una_linea {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (E C : ℝ≥0)
    (he : (n:ℝ≥0)*A.eps≤E) (ho : (n:ℝ≥0)*A.off≤2*C) (hb : (n:ℝ≥0)*A.bal≤C)
    (j : Vertex) (alive : activeLine X j) (e : Cell n) :
    let risk:=realRate masas X w (·⁻¹) j+virtRate masas X w (·⁻¹) j
    within masas ((n:ℝ≥0)^2*risk) ((n:ℝ≥0)*A.time⁻¹) (constanteUna A.l A.M C*(E+1)) := by
  intro risk
  have near:=(A.estimates reci orden j alive e).2.2.1
  rw [ns_real] at near
  have scaled:=scale masas (n:ℝ≥0) near
  apply grow masas _ (presupuesto_escalado A E C he ho hb)
  change within masas (n*((n:ℝ≥0)*risk)) (n*A.time⁻¹) ((n:ℝ≥0)*A.combined) at scaled
  simpa only [pow_two,mul_assoc] using scaled
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.dos_lineas_en_una_eleccion
#print axioms ArticuloA.Historias.riesgo_de_una_linea
