import RelojDelCoeficienteDeCadaPatron
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

def terminoInverso {n} (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (y z : ℝ≥0)
    (t : CuatroMarcas) (u : Mark n) := w (corners u).1*coefDelPerfil h p y z u t
def velocidadDelPerfil {n} (h : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (y z : ℝ≥0)
    (t : CuatroMarcas) (u : Mark n) := w (corners u).1*coefDelPerfil h p 1 1 u t*pendienteTemporal y z t
def constanteRelojInverso (κ m : ℝ≥0) (ζ W : ℝ) :=
  W*(↑((max 1 (m^4/κ^4))^4):ℝ)*(27*(cotaRelojComun ζ)^4)

theorem paso_del_coeficiente_fisico {n h} {p : FactoresContinuos} {κ m : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (w : Cell n→ℝ) (W : ℝ) (cap : ∀ z,|w z|≤W)
    {y z y' z' : ℝ≥0} {ζ d : ℝ} (dp : 0≤d) (dy : d≤y) (yt : y≤1) (zp : 0<ζ) (cut : ζ≤(z:ℝ)-d)
    (stepy : (y':ℝ)=(y:ℝ)-d) (stepz : (z':ℝ)=(z:ℝ)-d) (t : CuatroMarcas) (u : Mark n) :
    PasoDelReloj (terminoInverso h p w y z t u) (velocidadDelPerfil h p w y z t u)
      (terminoInverso h p w y' z' t u) d (constanteRelojInverso κ m ζ W*(escalaDelPatron n t:ℝ)) := by
  let X:=w (corners u).1*coefDelPerfil h p 1 1 u t
  let K:=27*(cotaRelojComun ζ)^4
  let M:=max (1:ℝ≥0) (m^4/κ^4)
  have yt' : (y:ℝ)≤1 := by exact_mod_cast yt
  have dyn:=escalar_paso (reloj_de_las_dieciseis_marcas dp dy yt' zp cut t) X
  have old : X*formaTemporal y z t=terminoInverso h p w y z t u := by
    unfold terminoInverso; rw [separacion_espacial_temporal]; dsimp [X]; ring
  have neweq : X*formaTemporal ((y:ℝ)-d) ((z:ℝ)-d) t=terminoInverso h p w y' z' t u := by
    rw [←stepy,←stepz]; unfold terminoInverso; rw [separacion_espacial_temporal]; dsimp [X]; ring
  rw [old,neweq] at dyn
  have base:=cota_de_coeficientes_del_articulo (h:=h) (ζ:=1) (z:=1) (y:=1) hn sp kp zero_lt_one le_rfl le_rfl u t
  have bb : |coefDelPerfil h p 1 1 u t|≤(↑(M^4):ℝ)*(escalaDelPatron n t:ℝ) := by
    simpa [M,show ∀ a : ℝ≥0,a^2*a^2=a^4 from fun a => by ring] using base
  have ww : 0≤W := (abs_nonneg _).trans (cap (corners u).1)
  apply ampliar_paso dyn dp
  rw [abs_mul]
  have scale:=mul_le_mul (cap (corners u).1) bb (abs_nonneg _) ww
  exact (mul_le_mul_of_nonneg_right scale (show 0≤K by dsimp [K]; positivity)).trans_eq (by
    dsimp [constanteRelojInverso,M,K]; ring)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.paso_del_coeficiente_fisico
