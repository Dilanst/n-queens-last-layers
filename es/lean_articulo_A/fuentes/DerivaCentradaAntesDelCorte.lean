import BlancoMovilDelPasoReal
import DerivaComunDeLaTransicion
import SeguimientoDeLosObservables
import DescomposicionEnLaHistoriaDetenida
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def coefSeguimiento (m κ ζ C : ℝ≥0) :=
  coefTransicion m (piso κ ζ) (techo m κ ζ) C + 4/ζ + 6*(1+m^4+2*m)/ζ^2

theorem deriva_centrada_fisica {n h : ℕ} {p : FactoresContinuos} {κ m ζ z u C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E)
    (t : ℕ) (ok : X.failed=false) (paso : u+(↑(2*n-1):ℝ≥0)⁻¹=z) (c : Coord) (cerca : within masas (lectura p h X c) (blanco (n:=n) p h c z) E) :
    let w:=coloresDelPerfil n h p
    let siguiente:=avg masas (kernel masas w (·⁻¹) t X) (fun Y => lectura p h Y c)
    |(siguiente:ℝ) - lectura p h X c - ((blanco (n:=n) p h c u:ℝ) - blanco (n:=n) p h c z)| ≤
      (coefSeguimiento m κ ζ C*(E+1)/n).val := by
  intro w siguiente
  have pos : 0<n := by omega
  have nN : (n:ℝ≥0)≤(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : n≤2*n-1)
  have Np : 0<(↑(2*n-1):ℝ≥0) := by exact_mod_cast (by omega : 0<2*n-1)
  have num : X.reals+X.virtuals≠0 := by
    intro eq; have ne:=(mul_pos Np (zp.trans_le hz)).ne'
    apply ne; rw [←reg.reloj,eq,Nat.cast_zero]
  let loss:=avg masas (choices masas X w (·⁻¹)) (perdidaFisica X (vInicial p) w c)
  have conservation : siguiente+loss=lectura p h X c :=
    media_siguiente_mas_perdida t X (vInicial p) w c ok num
  have physical:=perdida_media_en_el_estado hn hh sp kp m1 zp hz z1 bal he ho X reg c
  have ord : ordenFisico c≤4 ∧ Trayectoria.Adjunto.pairsN (ordenFisico c)≤6 := by cases c <;> simp only [ordenFisico] <;> decide
  have q:=resto_del_blanco (ordenFisico c) pos nN zp hz z1 paso ord.1 ord.2
    (lectura_inicial_acotada (p:=p) pos hh sp m1 c) cerca physical
  have bound : |(loss:ℝ)+↑(blanco (n:=n) p h c u)-↑(blanco (n:=n) p h c z)|≤(coefSeguimiento m κ ζ C*(E+1)/n).val := q
  have fr:=congrArg NNReal.toReal conservation
  simp only [NNReal.coe_add] at fr
  have dual (a l y v z : ℝ) (eq : a+l=y) : |a-y-(v-z)|=|l+v-z| := by
    rw [←abs_neg (l+v-z)]; congr 1; linarith
  rwa [dual _ _ _ _ _ fr]

theorem media_del_paso_activo {n} (p : FactoresContinuos) (h : ℕ) (X : State n)
    (t j : ℕ) (halt : ℕ→State n→Bool) (go : halt t X=false) (c : Coord) :
    avg masas (pasoParado (coloresDelPerfil n h p) halt j (t,X)) (fun y => lectura p h y.2 c)=
    avg masas (kernel masas (coloresDelPerfil n h p) (·⁻¹) t X) (fun Y => lectura p h Y c) := by
  unfold pasoParado stopped
  simp only [go,Bool.false_eq_true,if_false,avg_push]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_centrada_fisica
#print axioms ArticuloA.Historias.media_del_paso_activo
