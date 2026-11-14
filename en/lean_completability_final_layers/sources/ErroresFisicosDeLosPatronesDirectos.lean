import TransicionAntesDeLaPrimeraSalida
import DerivaEnRegion
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section
open Classical

theorem errores_de_los_patrones {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (nn : 0<n)
    (coh : coherent X) (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (z e : Cell n) (m : Marks) :
    let row:=choices masas X w (·⁻¹)
    let b:=(n:ℝ≥0)⁻¹*A.combined
    let d:=((n:ℝ≥0)^2)⁻¹*A.budget
    let rate:=referenceRate ((n:ℝ≥0)⁻¹*A.time⁻¹)
      (fun j => (n:ℝ≥0)⁻¹*(A.time⁻¹*A.p (side j,key z e j))) m
    let idealBirth:=((n:ℝ≥0)^2)⁻¹*A.birth e
    let pres:=fun occ => meanN masas row (fun _ => Repair.indicator (pattern occ X z e m))
    let fut:=fun occ => meanN masas row (fun i => Repair.indicator (pattern occ (next X i) z e m))
    let loss:=fun occ => weightedSingles masas occ X z e m rate
    ∃ pair : ℝ≥0,
      (n:ℝ≥0)^2*pair≤A.mr/A.l+4*(A.mv/A.l^4) ∧
      (n:ℝ≥0)^2*b≤constanteUna A.l A.M C*(E+1) ∧
      (n:ℝ≥0)^3*d≤constanteUna A.l A.M C*(E+1) ∧
      within masas (fut true+loss true) (pres true+(if availPattern X z e m then idealBirth else 0))
        (4*(if occupied X z e m then b else 0)+( (if availPattern X z e m then d else 0)+
          (↑(Repair.indicator (occupied X z e m)*6):ℝ≥0)*pair)) ∧
      within masas (fut false+loss false) (pres false)
        (8*b+(↑(Repair.indicator (availPattern X z e m)*28):ℝ≥0)*pair) := by
  intro row b d rate idealBirth pres fut loss
  obtain ⟨pair,top,oc,av⟩:=A.pattern_drift coh (fun _ h => inv_mul_cancel₀ h)
    (fun _ h => le_antisymm h (zero_le _)) z e m
  have np : (n:ℝ≥0)≠0 := by exact_mod_cast nn.ne'
  have un:=presupuesto_escalado A E C he ho hb
  have bnd : A.budget≤A.combined := by
    change A.budget≤(A.budget+A.vBudget)+A.time⁻¹*A.bal
    exact (le_add_of_nonneg_right (zero_le _)).trans (le_add_of_nonneg_right (zero_le _))
  have order : (n:ℝ≥0)*A.budget≤constanteUna A.l A.M C*(E+1) := (mul_le_mul_left' bnd _).trans un
  refine ⟨pair,?_,?_,?_,?_,?_⟩
  · have f : masas.four (fun _ => A.l)=A.l^4 := by change (A.l*A.l)*(A.l*A.l)=_; ring
    simp only [times_m,ns_real,Nat.cast_mul,f] at top
    change (n:ℝ≥0)*n*pair≤A.l⁻¹*A.mr+(4:ℝ≥0)*((A.l^4)⁻¹*A.mv) at top
    simpa only [pow_two,div_eq_mul_inv,mul_comm] using top
  · change (n:ℝ≥0)^2*((n:ℝ≥0)⁻¹*A.combined)≤_
    rwa [show (n:ℝ≥0)^2*((n:ℝ≥0)⁻¹*A.combined)=n*A.combined by field_simp; ring]
  · change (n:ℝ≥0)^3*(((n:ℝ≥0)^2)⁻¹*A.budget)≤_
    rwa [show (n:ℝ≥0)^3*(((n:ℝ≥0)^2)⁻¹*A.budget)=n*A.budget by field_simp; ring]
  · simp only [times_m,ns_real] at oc
    simpa only [row,b,d,rate,idealBirth,pres,fut,loss,pow_two] using oc
  · simp only [times_m,ns_real] at av
    simpa only [row,b,rate,pres,fut,loss] using av
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.errores_de_los_patrones
