import MediaDelIncrementoLinealInverso
import SaltoYErrorEnElRelojDeE2
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
def valorInversoAlTiempo {n} (h T : ℕ) (p : FactoresContinuos) (w : Cell n→ℝ) (t : ℕ) (X : State n) :=
  totalPonderado X (terminoInverso h p w (horizonteInverso n T t) (fraccionAntes n t))

def cotaDerivaInversa (κ m ζ C E : ℝ≥0) (W : ℝ) : ℝ :=
  let K:=constanteRelojInverso κ m ζ W
  let D : ℝ≥0:=constanteUna (piso κ ζ) (techo m κ ζ) C*(E+1)
  let H : ℝ≥0:=m^4/piso κ ζ+4*(m^4/(piso κ ζ)^4)
  176*K+K*(192*(D:ℝ)+720*(H:ℝ))

theorem deriva_del_observable_inverso {n h T t} {p : FactoresContinuos} {κ m ζ C E : ℝ≥0} {L W : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (tT : t<T) (finT : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X (fraccionAntes n t) E)
    (coh : coherent X) (run : X.failed=false) (w : Cell n→ℝ) (wp : 0≤W) (cap : ∀ z,|w z|≤W) :
    |media (choices masas X (coloresDelPerfil n h p) (·⁻¹))
      (fun a => valorInversoAlTiempo h T p w (t+1) (next X a)-valorInversoAlTiempo h T p w t X)|
      ≤cotaDerivaInversa κ m ζ C E W := by
  let z:=fraccionAntes n t
  let y:=horizonteInverso n T t
  let c:=terminoInverso h p w y z
  let d:=(↑(2*n-1):ℝ)⁻¹
  let V:=fun j u => d*velocidadDelPerfil h p w y z j u
  let row:=choices masas X (coloresDelPerfil n h p) (·⁻¹)
  let Δ:=fun a => valorInversoAlTiempo h T p w (t+1) (next X a)-valorInversoAlTiempo h T p w t X
  let K:=constanteRelojInverso κ m ζ W
  have hz:=fraccion_antes_del_horizonte tT.le floor
  have z1:=fraccion_a_lo_sumo_uno hn t
  let A:=region_del_estado hn hh sp kp m1 zp hz z1 bal he ho X reg
  have nr : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have clock : d=((n:ℝ)*(A.c:ℝ))⁻¹ := by
    change _=((n:ℝ)*(↑(relojIni n):ℝ))⁻¹
    simp only [relojIni,NNReal.coe_div,NNReal.coe_natCast]
    have prod : (↑(2*n-1):ℝ)=(n:ℝ)*((↑(2*n-1):ℝ)/n) := by field_simp [nr]
    exact congrArg (fun r : ℝ => r⁻¹) prod
  have hp (e : Cell n) : (A.piN e:ℝ)/n=(probDeLaCasilla h p e:ℝ) := by
    change (probArista n h p e:ℝ)/n=_
    simp [probDeLaCasilla]
  have cancel (u : Mark n) (_ : u∈paresCompatibles n) := cancelar_velocidad_y_generador A h p w u y z d
    rfl clock hp (fun _ => rfl)
  have mean:=media_lineal_de_la_jugada A run c V cancel
  have err:=promedio_de_un_resto row (normalizacion_en_la_region A run) (fun a => Δ a-linealDeUnaJugada X c V a)
    (176*K) (fun i hi => (salto_y_resto_en_el_reloj hn sp kp w wp cap zp tT finT floor X i.2 coh
      (row_allowed masas X _ _ i hi)).2)
  rw [media_de_diferencias] at err
  obtain ⟨dp,dy,yt,sy,sz,_⟩:=reloj_hasta_un_horizonte hn tT finT
  have cut : (ζ:ℝ)≤(z:ℝ)-d := by
    rw [←sz]; exact_mod_cast fraccion_antes_del_horizonte (Nat.succ_le.mpr tT) floor
  have coeff (j) (u : Mark n) (_ : u∈paresCompatibles n) :=
    (paso_del_coeficiente_fisico (h:=h) hn sp kp w W cap dp dy yt (show (0:ℝ)<ζ from zp) cut sy sz j u).old
  have pos : 0≤K := by dsimp only [K,constanteRelojInverso]; positivity
  have drift:=deriva_inversa_sumada hn hh sp kp m1 zp hz z1 bal he ho X reg coh.1 coh run K pos c coeff
  change media row (linealDeUnaJugada X c V)=_ at mean
  change |media row Δ|≤_
  calc _ ≤ |media row Δ-media row (linealDeUnaJugada X c V)|+|media row (linealDeUnaJugada X c V)| := by
          simpa only [sub_add_cancel] using abs_add_le (media row Δ-media row (linealDeUnaJugada X c V))
            (media row (linealDeUnaJugada X c V))
       _ ≤ _ := add_le_add err (by rw [mean]; exact drift)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_del_observable_inverso
