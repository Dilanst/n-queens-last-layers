import TransicionAntesDeLaPrimeraSalida
import TendenciaDeRegion
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def parMax (A B l : ℝ≥0) := A/l+4*(B/l^4)
def margenSoporte (D S E : ℝ≥0) := 6*D+4*S*(E+1)

theorem deriva_de_un_soporte {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (nn : 0<n)
    (E C : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (keep : Cell n→Bool) (o : Option (Fin 4)) :
    let F:=families o
    let M:=massGate masas X A.v keep F
    let lost:=avg masas (choices masas X w (·⁻¹)) (lostGate masas X A.v keep F)
    let deg:ℝ≥0:=if o.isSome then 3 else 4
    let D:=parMax A.mr A.mv A.l
    let S:=constanteUna A.l A.M C
    within masas lost (M*(deg*((n:ℝ≥0)⁻¹*A.time⁻¹))) (M*(margenSoporte D S E/(n:ℝ≥0)^2)) := by
  intro F M lost deg D S
  obtain ⟨pair,pc,tr⟩:=A.supports_drift (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
  have f : masas.four (fun _ => A.l)=A.l^4 := by change (A.l*A.l)*(A.l*A.l)=_; ring
  simp only [times_m,ns_real,Nat.cast_mul,f] at pc
  change (n:ℝ≥0)*n*pair≤A.l⁻¹*A.mr+(4:ℝ≥0)*((A.l^4)⁻¹*A.mv) at pc
  have pp : (n:ℝ≥0)^2*pair≤D := by simpa only [D,parMax,pow_two,div_eq_mul_inv,mul_comm] using pc
  have ss:=presupuesto_escalado A E C he ho hb
  have np : 0<(n:ℝ≥0) := by exact_mod_cast nn
  have bp : pair≤D/(n:ℝ≥0)^2 := (le_div_iff₀ (pow_pos np 2)).mpr (by simpa only [mul_comm] using pp)
  have sb : (n:ℝ≥0)⁻¹*A.combined≤S*(E+1)/(n:ℝ≥0)^2 := by
    apply (le_div_iff₀ (pow_pos np 2)).mpr
    rwa [show ((n:ℝ≥0)⁻¹*A.combined)*(n:ℝ≥0)^2=n*A.combined by field_simp; ring]
  have bound (r j : ℝ≥0) (r6 : r≤6) (j4 : j≤4) :
      r*pair+j*((n:ℝ≥0)⁻¹*A.combined)≤margenSoporte D S E/(n:ℝ≥0)^2 := by
    calc _ ≤ 6*(D/(n:ℝ≥0)^2)+4*(S*(E+1)/(n:ℝ≥0)^2) := add_le_add (mul_le_mul' r6 bp) (mul_le_mul' j4 sb)
         _ = _ := by unfold margenSoporte; simp only [div_eq_mul_inv]; ring
  have v:=tr keep o
  simp only [times_m,ns_real] at v
  cases o with
  | none =>
    apply grow masas v
    exact mul_le_mul_left' (bound 6 4 le_rfl le_rfl) M
  | some j =>
    apply grow masas v
    exact mul_le_mul_left' (bound 3 3 (by norm_num) (by norm_num)) M

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_de_un_soporte
