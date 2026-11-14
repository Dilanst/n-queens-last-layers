import DerivaFisicaDeLosSoportes
import MasasVivasPorCoordenada
import InnovacionBilateralDeE2
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def ordenFisico : Coord → ℕ
  | .realCount | .family _ => 1
  | .degree _ => 3
  | .boardWeight => 4

def perdidaFisica {n} (X : State n) (v : Cell n → ℝ≥0) (w : ColorWeights ℝ≥0) :
    Coord → Choice n → ℝ≥0
  | .realCount,a => ↑(X.reals-(next X a).reals)
  | .family i,a => lostWeight masas X w i a
  | .degree j,a => lostGate masas X v (fun e => hitsVertex (lines e) j) (families (some j.1)) a
  | .boardWeight,a => (n:ℝ≥0)⁻¹*lostGate masas X v (fun _ => true) (families none) a

theorem balance_de_coordenada {n} (X : State n) (v : Cell n → ℝ≥0) (w : ColorWeights ℝ≥0)
    (c : Coord) (a : Choice n) :
    observed masas (·⁻¹) v w (next X a) c + perdidaFisica X v w c a = observed masas (·⁻¹) v w X c := by
  cases c with
  | realCount =>
    simp only [observed,perdidaFisica,ns_real,←Nat.cast_add]
    have h : (next X a).reals≤X.reals := by cases a <;> simp [next]
    exact_mod_cast (by omega : (next X a).reals+(X.reals-(next X a).reals)=X.reals)
  | family i => exact family_step masas X w i a
  | degree j =>
    have h:=mass_balance masas X v (fun e => hitsVertex (lines e) j) (families (some j.1)) a
    rw [(identities masas X v j).2,(identities masas (next X a) v j).2] at h
    exact h
  | boardWeight =>
    have h:=mass_balance masas X v (fun _ => true) (families none) a
    rw [(identities masas X v (0,0)).1,(identities masas (next X a) v (0,0)).1] at h
    simp only [observed,Trayectoria.E2.Regular.norm,ns_real,perdidaFisica]
    change _⁻¹*_+_⁻¹*_= _⁻¹*_
    rw [←mul_add]; exact congrArg (fun m => (n:ℝ≥0)⁻¹*m) h

private theorem media_del_entero {ι} (row : Atoms ℝ≥0 ι) (f : ι → ℕ) :
    meanN masas row f=avg masas row (fun i => (f i:ℝ≥0)) := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    change masas.times (f a.2) a.1 + meanN masas l f = a.1*(f a.2:ℝ≥0)+_
    rw [times_m,ns_real,ih]; change _*_+_=_*_+_; rw [mul_comm (↑(f a.2):ℝ≥0)]; rfl

theorem perdida_media_real {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) :
    avg masas (choices masas X w (·⁻¹)) (perdidaFisica X A.v w .realCount) =
      (X.reals:ℝ≥0)*((n:ℝ≥0)⁻¹*A.time⁻¹) := by
  obtain ⟨_,_,rr,vv⟩:=A.raw_floors (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
  have h:=colour_drift masas X w (·⁻¹) (fun _ h => inv_mul_cancel₀ h) rr vv
  rw [media_del_entero] at h
  have N : (n:ℝ≥0)≠0 := by simpa only [ns_real] using A.sizePos
  have clock : (n:ℝ≥0)⁻¹*((X.reals:ℝ≥0)+X.virtuals)=A.time := by
    simpa only [Trayectoria.E2.Regular.norm,timeMass,ns_real] using A.clock
  rw [←clock]; unfold quota at h
  change _ = (ns masas X.reals+ns masas X.virtuals)⁻¹*ns masas X.reals at h
  rw [ns_real,ns_real] at h
  rw [show (n:ℝ≥0)⁻¹*((n:ℝ≥0)⁻¹*((X.reals:ℝ≥0)+X.virtuals))⁻¹ =
    ((X.reals:ℝ≥0)+X.virtuals)⁻¹ by rw [mul_inv_rev,inv_inv]; field_simp]
  exact h.trans (mul_comm _ _)

theorem media_siguiente_mas_perdida {n} (t : ℕ) (X : State n) (v : Cell n→ℝ≥0)
    (w : ColorWeights ℝ≥0) (c : Coord) (ok : X.failed=false) (num : X.reals+X.virtuals≠0) :
    avg masas (kernel masas w (·⁻¹) t X) (fun Y => observed masas (·⁻¹) v w Y c) +
    avg masas (choices masas X w (·⁻¹)) (perdidaFisica X v w c) = observed masas (·⁻¹) v w X c := by
  rw [kernel_is_row masas X t w _ ok num,avg_push]
  have norm:=choices_total masas X t w (·⁻¹) (fun _ h => inv_mul_cancel₀ h) (by
    intro i j nz; change ns masas i+ns masas j≠0
    rw [ns_real,ns_real,←Nat.cast_add]; exact_mod_cast nz) ok num
  change masas.add (avg masas _ _) (avg masas _ _)=_
  rw [←avg_plus]
  have eq (a : Choice n) := balance_de_coordenada X v w c a
  change avg masas _ (fun a => observed masas _ v w (next X a) c + perdidaFisica X v w c a)=_
  simp_rw [eq]; rw [avg_constant,norm]; exact one_mul _

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_siguiente_mas_perdida
#print axioms ArticuloA.Historias.perdida_media_real
