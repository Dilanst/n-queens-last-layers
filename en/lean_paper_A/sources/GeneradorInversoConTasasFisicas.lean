import LasDiezIntensidadesDelGenerador
import RestoDeLosDieciseisPatrones
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def nacimientoCondicionado (P : Prop) (r : ℝ≥0) : ℝ≥0 := if P then r else 0

/-- Finite signed drift, on the unconditioned kernel before the cutoff.
Both hazards for a vacant target only involve the promoted pre-move pattern. -/
theorem generador_fisico_del_par {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (o v j l : Bool) (ok : compatible e f) (coh : coherent X)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0)
    (running : X.failed=false) (rem : X.reals+X.virtuals≠0) :
    let row:=choices masas X w (·⁻¹)
    let U:=patronInverso X e f o v j l
    let r:=realAtom masas X w (·⁻¹)
    let d:=fun a => deathsOn (diez e f) (golpeDelPar e f o v j l a)
    (↑(meanN masas row (fun a => indicator (patronInverso (next X a) e f o v j l))):ℝ)-(indicator U:ℝ)=
      (nacimientoCondicionado (o=true ∧ patronInverso X e f false v j l) (r e):ℝ)+
      (nacimientoCondicionado (v=true ∧ patronInverso X e f o false j l) (r f):ℝ)-
      (bajasFuente X w e U o:ℝ)-(bajasFuente X w f U v:ℝ)-(bajasDestino X w e f o v j l:ℝ)+
      (↑(meanN masas row (fun a => indicator U*(d a-1))):ℝ) := by
  intro row U r d
  have bal:=deriva_media_del_patron X w e f o v j l ok coh rr vv running rem
  dsimp only at bal
  rw [descomponer_intensidades X w e f o v j l ok coh rr vv] at bal
  have eq:=congrArg (fun y : ℝ≥0 => (y:ℝ)) bal
  push_cast at eq
  dsimp only [row,U,r,d,nacimientoCondicionado]
  split_ifs at eq ⊢ <;> push_cast at eq ⊢ <;> linarith only [eq]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.generador_fisico_del_par
